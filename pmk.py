# -*- coding: utf-8 -*-
"""
프메 엔딩 저울 — Princess Maker: Children of Revelation 세이브 분석기
표준 파이썬만 있으면 동작합니다 (추가 설치 불필요).

사용법
    python pmk.py                 최신 세이브 자동 분석
    python pmk.py --list          세이브 슬롯 목록
    python pmk.py slot_3          특정 슬롯 분석
    python pmk.py --target 여왕   목표 엔딩 지정 (기본: 여왕)
    python pmk.py account         계정 전체 진행도
    python pmk.py --steamid <ID>  Steam64 ID 직접 지정
    python pmk.py --once          한 번만 출력하고 종료
"""
import sys, os, glob, json, gzip, base64, struct, datetime, hashlib

# 키 유도용 시드 (게임 공통 상수)
_SEED = bytes([250,46,122,58,65,111,8,229,53,168,219,104,9,11,43,137,238,57,113,114,
               117,133,159,220,221,56,147,44,64,232,251,219,46,94,85,46,158,100,235,45])

def save_key(steam_id):
    """세이브 파일 복호화 키 — Steam64 ID마다 다릅니다."""
    return hashlib.sha256(_SEED + str(steam_id).encode()).digest()[:16]

# ───────────────────────── AES-128/256 CBC (순수 파이썬) ─────────────────────────
_SB = bytes.fromhex(
 '637c777bf26b6fc53001672bfed7ab76ca82c97dfa5947f0add4a2af9ca472c0'
 'b7fd9326363ff7cc34a5e5f171d8311504c723c31896059a071280e2eb27b275'
 '09832c1a1b6e5aa0523bd6b329e32f8453d100ed20fcb15b6acbbe394a4c58cf'
 'd0efaafb434d338545f9027f503c9fa851a3408f929d38f5bcb6da2110fff3d2'
 'cd0c13ec5f974417c4a77e3d645d197360814fdc222a908846eeb814de5e0bdb'
 'e0323a0a4906245cc2d3ac629195e479e7c8376d8dd54ea96c56f4ea657aae08'
 'ba78252e1ca6b4c6e8dd741f4bbd8b8a703eb5664803f60e613557b986c11d9e'
 'e1f8981169d98e949b1e87e9ce5528df8ca1890dbfe6426841992d0fb054bb16')
_ISB = [0]*256
for i,v in enumerate(_SB): _ISB[v]=i
_ISB = bytes(_ISB)
_RCON = [0x01,0x02,0x04,0x08,0x10,0x20,0x40,0x80,0x1b,0x36,0x6c,0xd8,0xab,0x4d]

def _xt(a):
    a <<= 1
    return (a ^ 0x1b) & 0xff if a & 0x100 else a
def _mul(a,b):
    r=0
    while b:
        if b&1: r^=a
        a=_xt(a); b>>=1
    return r

def _expand(key):
    nk=len(key)//4; nr=nk+6
    w=[list(key[4*i:4*i+4]) for i in range(nk)]
    for i in range(nk, 4*(nr+1)):
        t=list(w[i-1])
        if i%nk==0:
            t=t[1:]+t[:1]
            t=[_SB[x] for x in t]
            t[0]^=_RCON[i//nk-1]
        elif nk>6 and i%nk==4:
            t=[_SB[x] for x in t]
        w.append([w[i-nk][j]^t[j] for j in range(4)])
    return w, nr

def _dec_block(blk, w, nr):
    s=[list(blk[i::4]) for i in range(4)]  # column-major -> row-major
    def ark(rnd):
        for c in range(4):
            k=w[rnd*4+c]
            for r in range(4): s[r][c]^=k[r]
    ark(nr)
    for rnd in range(nr-1,-1,-1):
        for r in range(1,4): s[r]=s[r][-r:]+s[r][:-r]          # inv shift rows
        for r in range(4): s[r]=[_ISB[x] for x in s[r]]        # inv sub bytes
        ark(rnd)
        if rnd:
            for c in range(4):                                  # inv mix columns
                a=[s[r][c] for r in range(4)]
                s[0][c]=_mul(a[0],14)^_mul(a[1],11)^_mul(a[2],13)^_mul(a[3],9)
                s[1][c]=_mul(a[0],9)^_mul(a[1],14)^_mul(a[2],11)^_mul(a[3],13)
                s[2][c]=_mul(a[0],13)^_mul(a[1],9)^_mul(a[2],14)^_mul(a[3],11)
                s[3][c]=_mul(a[0],11)^_mul(a[1],13)^_mul(a[2],9)^_mul(a[3],14)
    out=bytearray(16)
    for c in range(4):
        for r in range(4): out[c*4+r]=s[r][c]
    return bytes(out)

def aes_cbc_decrypt(key, iv, ct):
    w,nr=_expand(key)
    out=bytearray(); prev=iv
    for i in range(0,len(ct),16):
        blk=ct[i:i+16]
        d=_dec_block(blk,w,nr)
        out += bytes(x^y for x,y in zip(d,prev))
        prev=blk
    pad=out[-1]
    if 1<=pad<=16: out=out[:-pad]
    return bytes(out)

# ───────────────────────── MessagePack 디코더 ─────────────────────────
class _MP:
    def __init__(self,b): self.b=b; self.p=0
    def u(self,fmt,n):
        v=struct.unpack_from(fmt,self.b,self.p)[0]; self.p+=n; return v
    def raw(self,n):
        v=self.b[self.p:self.p+n]; self.p+=n; return v
    def rd(self):
        c=self.b[self.p]; self.p+=1
        if c<=0x7f: return c
        if c>=0xe0: return c-256
        if c&0xf0==0x80: return {self.rd():self.rd() for _ in range(c&0x0f)}
        if c&0xf0==0x90: return [self.rd() for _ in range(c&0x0f)]
        if c&0xe0==0xa0: return self.raw(c&0x1f).decode('utf-8','replace')
        if c==0xc0: return None
        if c==0xc2: return False
        if c==0xc3: return True
        if c==0xc4: return self.raw(self.u('>B',1))
        if c==0xc5: return self.raw(self.u('>H',2))
        if c==0xc6: return self.raw(self.u('>I',4))
        if c==0xc7: n=self.u('>B',1); t=self.u('>b',1); return self.ext(t,n)
        if c==0xc8: n=self.u('>H',2); t=self.u('>b',1); return self.ext(t,n)
        if c==0xc9: n=self.u('>I',4); t=self.u('>b',1); return self.ext(t,n)
        if c==0xca: return self.u('>f',4)
        if c==0xcb: return self.u('>d',8)
        if c==0xcc: return self.u('>B',1)
        if c==0xcd: return self.u('>H',2)
        if c==0xce: return self.u('>I',4)
        if c==0xcf: return self.u('>Q',8)
        if c==0xd0: return self.u('>b',1)
        if c==0xd1: return self.u('>h',2)
        if c==0xd2: return self.u('>i',4)
        if c==0xd3: return self.u('>q',8)
        if c==0xd4: t=self.u('>b',1); return self.ext(t,1)
        if c==0xd5: t=self.u('>b',1); return self.ext(t,2)
        if c==0xd6: t=self.u('>b',1); return self.ext(t,4)
        if c==0xd7: t=self.u('>b',1); return self.ext(t,8)
        if c==0xd8: t=self.u('>b',1); return self.ext(t,16)
        if c==0xd9: return self.raw(self.u('>B',1)).decode('utf-8','replace')
        if c==0xda: return self.raw(self.u('>H',2)).decode('utf-8','replace')
        if c==0xdb: return self.raw(self.u('>I',4)).decode('utf-8','replace')
        if c==0xdc: return [self.rd() for _ in range(self.u('>H',2))]
        if c==0xdd: return [self.rd() for _ in range(self.u('>I',4))]
        if c==0xde: n=self.u('>H',2); return {self.rd():self.rd() for _ in range(n)}
        if c==0xdf: n=self.u('>I',4); return {self.rd():self.rd() for _ in range(n)}
        raise ValueError('알 수 없는 MessagePack 코드 0x%02x' % c)
    def ext(self,t,n):
        d=self.raw(n)
        if t==-1:
            if n==4: return {'__ts':struct.unpack('>I',d)[0]}
            if n==8:
                v=struct.unpack('>Q',d)[0]; return {'__ts':v & 0x3ffffffff}
            if n==12: return {'__ts':struct.unpack('>q',d[4:])[0]}
        return {'__ext':t,'data':d}

def unpack(b): return _MP(b).rd()

def load_sav(path, steam_id):
    d=open(path,'rb').read()
    if d[:4]!=b'PMKT': raise ValueError('PMKT 세이브 파일이 아닙니다: '+os.path.basename(path))
    return unpack(aes_cbc_decrypt(save_key(steam_id), d[5:21], d[21:len(d)-32]))

# ───────────────────────── 색상 ─────────────────────────
if os.name=='nt':
    try:
        import ctypes; ctypes.windll.kernel32.SetConsoleMode(ctypes.windll.kernel32.GetStdHandle(-11),7)
    except Exception: pass
_C = sys.stdout.isatty() or os.name=='nt'
def c(s,code): return ('\033[%sm%s\033[0m'%(code,s)) if _C else str(s)
def dim(s): return c(s,'2')
def bold(s): return c(s,'1')
def ok(s): return c(s,'32')
def bad(s): return c(s,'31')
def warn(s): return c(s,'33')
def acc(s): return c(s,'35')
def strike(s): return c(s,'9;2')   # 취소선 + 흐리게

def w(s):
    """한글 폭 고려한 문자열 길이"""
    n=0
    for ch in str(s):
        n += 2 if ord(ch)>0x1100 and (0x1100<=ord(ch)<=0x115F or 0x2E80<=ord(ch)<=0xA4CF or 0xAC00<=ord(ch)<=0xD7A3 or 0xF900<=ord(ch)<=0xFAFF or 0xFE30<=ord(ch)<=0xFE6F or 0xFF00<=ord(ch)<=0xFF60 or 0xFFE0<=ord(ch)<=0xFFE6) else 1
    return n
def pad(s,n,right=False):
    s=str(s); d=max(0,n-w(s))
    return (' '*d+s) if right else (s+' '*d)

# ───────────────────────── 데이터 ─────────────────────────
DATA = json.loads(gzip.decompress(base64.b64decode("""H4sIAAAAAAACCrVdX3MTR7b/Klo/K7c0PTOSrZdb/E2yWba4gbv7QKUoxRa2ClnylWWyWWqrDAhKwWYxwQYDtq/YAIaUtyKwSOS7zt7vch81o+9wT/d093TPdM+0JG9VKoHozK/POX36/OvumZtTy81Sc2V5qnhzysL/uj5VnLrULC1WaqWp7FQN/uZ/6Hmd1/AX+H9TxRz8t/SnqeLMzMxfslMofKRRrs03F+gzw71t9QM2e+BCvVlvnPq6Uq00v6UPeT8d+x/eqZ9z2HOf15rlarUyX67NlhmD+6vefQ2DLh+vNF+ZZQPtt7US5fkD5VqzVI3I5Xe2/LWO9uECe/jTRomzN+h3h9+31Q9MswfOlmfrjZVFNsx22+9oHplhj5yp126UG8ulZqVeY2p/tum3O+rnrByfq3JtudKs3Ag1P+hu+O1tv/Ve86glPsrV3jr277/SPMEN48xCqbHI9f5KqzqLW8YpmN3aImifj/N++IQ/9YmdYw/Cn/CD3DTO3ahU2TNbd4dPvtOMxG3icqVRnquVl5fDmRL4+8TK8aHwH/Gj3DrOV+YXmuXGl+WllaY4A36n5d8+GD78btBdjQ7vBhgFySRL1RgGNs8PW4kY3G4u1WcrCgjgYfBxIxGC29GpRjP+PBhgu5P0POLm9GW5Sh5dXqgsXSw1wonzfl71fnzrP1v1d7czg97q4LAl6jZULYazVHBnVr5m1ja8teH119PAqGw5jnaq2SzNXmfze/hx8OGd3gRzKNTJYr3BxOi+85/0Ep7ilvvZRaa+O7vej3cVj2A7Cjh0JCuQ2AzmP5PKrezbJJYDhBTOXT6F50s36o3zK43GtxdKVaZx74e3w4cHWN3D7T54CO+hoHFpCbpWHOh8eTGE8u+88l4fG0EhCepsebFeE3jyt1pgkV6nDZ7HCM6Ow0mcDX7pAxqYqffGTFRHFrXeKC83RQa3DzDSVssIzFWASewNb/UAzjtqmSLmZXkbpXlJf1jc3WN/7RVm0lCFBQVkhMmDYEaGa10TREsIReB1yn8oVVcY1u9Li+Wr0v+VDDcAQNxILlwUnyN/U6w3eARnOV+Uv71c/3wOP8synCJwxkN8EWXltKRoZ+V8o+hkaSJRdLPRDKGYz9K4XyxkeUAvTmflSF2cyUoRGHjM0rhatICdIGAWLWAmjIRFC1gh8a1oAQ9h4CpawEg8GBWtfFYRX4oWcBYLGUULeJSjQNECLhWOvYhy2biHLiLgm7owEAf/hTgj+DNIAV4R/mBnJU8H/4fpktNiSWRHBP48G/cpRdfKRt1D0UXZ+BovunY2tlCLrpNVLLiiy8YXVk3RzWcVdl90sR5DK4WJA0bB/IoIYWObXSjPrWC6m1Of1RfJfytzxNiCfPWR/3TDb+1khjs9f213Ch453yiXL1dCUkRJ9zb8nc7w2Y738Bkm+0NptkQMMaCyWYTa9P/nO5yMYaRKuTp3NRCN0eXpQr2z4/faeIn6t7shbSAao3W4p/XftL29VUzr7b8WoPFUMGo3DDjYSbUFVDwPjKzAyfyX7zP+9q3hvQ4m/W3966uf1VeWuUTToYq2gNNjRvQliL3AiGYo2o/v/L3XjOKP9frcN/XG9UptnusbCYQHEE8hIDLyT0uNuTLnz6KahNnwDo79FxuM7PPatUpjsRQKjCeaUB5tez+s+/fWOYeg79JKo1TjWrcKIejaEaM7CxOzfGmhvsTJ6OzAvPh3bvkdPvb5xkolBLNYDgNx9Njv/jo45Bo8s1Cevb5UrwhD01kcfFj1DvoCl6ersPqWFytNrkyLTeH6Kmhz0G0x0lOzpbnyIhcc5ULDOOp5D7reT33OQOlaaORsdt5t+rs97/EOUA//us1IL6808WqntNOs/liFygoyVshb+XzC6mpca9RDoZAV5pWPfsCZKcMsgXvlc4nY2vnhmCrz3NzK1d9VAA4q3Ua4xNjqOegPt54xus8qy8BgKDVbDk//TnnDROealf9aKTebIdYMz5sh8WJkl8Ae5ziJy6cE12iU5EKp0QRvDN53mRPmed0tEZKwQ0kKUqUQcg843DfkWFXdF2DOSu6DKfSg5z9/xzGq4L6EeWdL8ml30G+LHK0shxzZTOm761B7ES8A66Fyo1S9eqZevx6uHkonUZwuNZvV0IByloJGkIwEEwVIDc9JSOQwIqCab4AtX16ApbdQr84th475Si5bW6lWw399Jfpi1a/cBat+FPzZlTzKWs50Fs3kslCWfCX5seBHJ4sgvji56a9izkZNIPk4NQnza+pfRSelphB9yRUIqhasAAQmaecZBXVL6h8F73bFAQKYBWsGCBAjEB2QmoJ6iCt2ITsDv01bWZtzx32S8tfADSl/Er3JFTDWaSDI57Nomo9KfUjsx6jzwEwDv1Y+l0W281XEayh/pX5A+ZvkADQUZOUrf+NrVfmr4KbUT+M1pfyFugk1P8G6j/0mJx7KhSWlG3oKmmEkQAS5hZJAdjtxEvAGDSHRvXJzap5kZlLd4FB/HnRAMv7Te+DYwN0QYkSJXV5lcPLdA3C3w62dDIRciCvsCZs+YfFHEHvE33vk765mvB/v4vYbpXcoPeL0NqP3nnT8baime979zYy/24d0hT3l0qdsNxSDjbLTgREwfRDFCH2eyyG0T3gygDnCtKDTcm0OPA7xmufIH6/CiqmS8uMmTUDf+23c8f2GqHKBeI+p4dY2JCkZf+1nLCHOWnZ7WJUelJ/veiSMBGh/qFSrpflyg8NBmrjbgvjt/XQcgCIOyjNDoAAwyJ8PhnttAYy43+vl8lKIh9OL2wcZv9OCOYGH7kJohbT2AGePAXyOtPpUQ3jbj+AfLMqHdWGULytBOsqU9fMqVL0BmCOBDQ7fQg7kvT7OeK3v4B9gNoO7YjvHoJtsxu/+EydU228zuE38fJ0Q3nsM2aW/D1axvwEVgDDs2fosTZ9CPWVoKgqTpRJmqzXcbIP2e1BzgAyUGsYRYM+UGktQ3gkzABkzm1AZz7u9DekCYROm8Ye38O+Md9iTJ/QSBNmKgHb4SORuWkALZhoLsb86vI3tAuoiUeDyMtTAIRQkyd7r7Yy3uYlLI8gvW22Giz0Rl/rehre2zSR+AulNH/dR8JLZ/iUDmocFBAoXBvpjqdJsCCYdJO1gMxu4GlApNhgCm0i3i1NSQJRMhOU9BO35Ju64cCUgV0SCnGltF5jNgCVh5+Hd2sXLBHMLBt7ZEkAvNsC5Ncs8i45lz5RTJJpgFzOH5x0jvtkYvO/6L1ZFY8ZJyYVSTVqDpLjCnVbSGesrbeHhM3A/3uNXUJTg9Q3/IYYB5nA7YhGXFyCALlWCkpRo5MUGJMvJtjv49Q5GHm69HfwD5nz/r8SPrO1AkQJ6F+1tBVY7ZDYh96z4yATVB6l577eHD/CWxfDOqkpNAWUmKLYl7/IbYSi5gAoLJ/zPbk9li7ywwpgwF4OjdaAUMX9XnwfNVGZDfwpafb2tUL64dAhNUAhmov7w3wT0U8vLgE7rUpbJfzzwX8K/N5SKECo8lTpE8P+sVesl/Keo+UgS7IXjOIIErI5TDSKqHFIkCEECeHdzeHfDe7CpQg3KPtpgGXz4dfiULFJ//TGwIbJOsrLPa8vNxoroVIP6LOM9bGH7B8v0PvBxnBlXiG5/h3I9g8nFeRVdSqMiuFQI9MFmSgxp0CcQ/h7Y6GMosroZf6dF/MDdPm7eC6u/VBG99PDZpgaS+NX1wT8eZnDH9w0xDtLqfhXz1STVk/xJUA5mZIcioQcEeMsQYimG/mfff7UqzxrBDVndbGEHvA/Br7uDO+7wl9sswNiSX/35FdHGz5veu27G2yK6GYLbJ/5bGIDkoRLjQfGZwDglSGYcXOxi6Wy9htvDEea9h20N19hdQsoHVOAAscOF4Pg4CDhPu/79jyLfOJ8/V5uv1MpSygMWh/d8oJoP10tB0gyrwLFTDEp/7NfEaIEXtpgLkbKkUqqFSx+3MaQhZAWR3zEbJKIdqxc9kUA2mWDDSb9aeKeCzM5aMMWt9/CnCPYZiBLNUvVcFdbO5UY9aJMR1tvbeE12tnCP5fCRt/aWjTPtCjrqYJ14L3f8571MsAqykFB9jyMHJPPD9Y1sJpp0gAMFdUCYCQLkLk69otJ+UcM9dllcvPSZnclJH/0dpinwJiRLAAe3toOjPEwTEOCUUspATs3dgBwMakwhBr8F7yUs8YIwxvDOBnNtkAn9QKwu4uGgFmuu1MqXy9Wq4IfAOYIJMVDbkhg/bGEOB7+QyQf+IHHCgfRd7/9W38RM4AzAXleYALiHMGeaieuFWsA2XuT+h50gh3oRYf7TOi7IxYxsmz2sWdzk0ARb3IH/x3tc94/IUFD6YNsgQ8E8B0XIv4uWt1CqLwcFtZCnDLePYdUTBLb8+Pg2krKVX3b8o2eQ5re9t/3oAzjKeRvbeDv2sBeR9MK3y+DUK1C3XF6olK/xQNTrBXtosZECnqDGfEDF9NotWPjYteNs/KgT5KK/kfOvT+tz10rNBcG8vv8FVyfgucDkOzv+sy2VSQz3tkkSRvUAhdO9DaLG/T1/76VSk+fLi8FOBlHg+o730+pwfX14h6bqtuzvg3iNHRk5HuJ3bsFcZfy/3cXT+AIn+URzkeDdpH3+4LRDz3v5PgOrHm9CQIJ3n2ZMtqOaoO4TZh1PcclFtix3N7w3gUvY/VU5SWcrS9X6YilMop71wRQhv1GtfwpMJwfyv7VOICD2RyTRf/xKOcqnZah1SlU5tRx87NJB5JBDqioQGqfEkF0Mt3qZ6MDgyMnA7TYZdbcdn6wv69+Wqn+s/LkUtKoD2bYGP9+iEQbCAR1dskFc9DICVmeJSywi2JenTl2E8qoyVxby0Gdb3ptf6VGTrWeYcVaQO5IJBiTYROm8Pe+SVQ15wdZOXCLSHfpCsA+sd2bcrowMv7R2iIq6m4Oj12wAauJgVz/1SVDY2yB9oD2FAiFfgEwn9FMkW+j6rX5wOuob0laR0+vwDMOzVZY6vliHsEN6Avg0wqMNplSY4r1Hgc/K+C97eCOL+BKF4P+xUi4Lof4gFFqeOggURz1qHqR0O9oB41EPT+bUbHihlRlPq4PdjIR0em+b+a+34BBwR6xPAmi/S5sNoC5aw7MtFho3oy477qgjgQKSjvW3BPXRBqTEoHoIxrjf4m/dJ9UUB8ApIoTEew+4oUULiDkpzSXVABjTQW+4e6DK4YJ8gCRwJIkOjJjUt4NuGzcm1t74O8fyQBfLjWsri0IIf9kdPnkdSleIFM1BurFOUv2uLA0dy9/9CHmXPMpvy9+UhTwBcgD82L0HkKf1sR9RD8erW9oAyAT7TUZynRZ9DjjGnQ72ZLzclZNfkroHisP7dUYDXKrMV6pnG6VrzXIkVfX3W6TE22rr5GIJ64gy0R2Ks2Uh6ZbqaZx7v1YWPgIZ80O7xzgrhUnkhQrNzcn/7kndppWlavmqeM7hpnwiKRhTSpW9DvGi8KN365iscKhh7rbCpovK7KWR2IGIm7HjStHhqF0G/ozl2ni4VewEU4cTD2XcVJ1liokHCcTeSzJkezvDKqTn74yEk0973Iwdc4oNtvcIn0LeX8elO+3ikdUNqcWLFo5fJjIKB19uCkfwooOB3eJsD/uv/XXcXCalH8xyd6T5E0/U3BSO6cVkCzqznVfE9QYpTNDxwItolCkMT+vcjJ3mi44qRtFM0M7z//GKlKQ0Q+unjnNVTAKSBoNA6f+NJGZkb6WPeyXmIslKFE8UxsbpvsVqw6Vpu+0dvaA1qLe2PooegzNXN4VjsbG1hkvB1yyzgOEGh4dEOvD5MImm0v2+3lgMk1EonyF2Y8sePvnOO/wYM8vD3vAeSTcHH7pQLhAj+d/24J/HWkFKlUU+PUeQW8ScBj7ZdAsnuLgZzw5NsRB2nMD657P15ZLogMF8ft3kvj7q50m5ttYBz4VbBy+CftzWOrUZ1RYHHeeLymKpUQlzP1go+221Q+JncUgq/raPt1HwyqX9bJikfh9vVey3dEJdWPlzqSJ26cgWSGwc2k583CUL9kEXqpvXEFNIAntnd9DvMfy/sK29S/QOyBV6kF7e5MvSHdImGaWJKeD/zZK/3SD/xucQc3hXUXiab+oJjyP6eHjbYZb8dIOc1FTjiPt5AtQ0hQpPXAhgDoVKxUISW5G7JRyObMMu4zw+gkd2AQWmCpJ6godp8q/kJ3w+YMRi+j1frX9Dfr16bslRKTuKRDcGNQoKD5YIjNkGULJ+YldiQqycRkMimC2BhZeM0lHC/UmNgOLBGAMRI3gowtgI8kWQIiLS2zLpMGzDVCOecCjHwMolMJS28Mx4Gn/u+A6uRrbwxJCBaDKYLBu7czUqS7Jo7L5SOgrfMdYIJpy1MjBJGQ2NaUcySkQy+b6YgW3jDeyRhHN1640jUT9nKRylRR6e1j+bsrhcrZsNIRzZn9E7gaGj10JI++4anbAfU604DmYWh7QzFQe0x1720mEA3eyTU4wGVh0HQ2M7kjhW3CDCa43peOGRBI2U9CilgZgRKHSSfNnJJqt335HtbYWQ4dlEAxmVeJH8QL7TOyaP44cauuGukVQ4xGnijwUsNJkfFaEmM1m2/6+REJ/nNBBNQhk30kggk0klnEDQCBYcRzXJXSNQaMzYHsUZN6+jhyBMxXKSxDoJkU5QHGfc5EvAcINswNVmA3FVCKc+NFoNzicbGEsUajK3HUUbN60Ujp+YCpiQZ0hQkwkYRTspAZ3JvGsUjtpUfhSbkk7k6LQejbyOORqKu2p6cH88vED1tiJdzBLqrL5SRzl9KRs9eSNogiXsqvcepEqgQZbNUXztgzDrI/Eq64WmDlmmhqwuP7FcbYLCD5bqKnN85cSkJpeBxnXiEZjJ4m4EzGwdshIpVqeFZ800C4jdkTHwzBGsCaujCJo9ZuASz4GNtzJQLhUTSZiqN4SMjmkreosC0dVzS1a8xWiAm1JM540V6ab235KxktOBWMWU5Ge16YB54RXFsSezXuHAucYHSRSpniiKN35BHkUat1INj79rBAxuHBrIFkGaoK8bQbIn7YOHh/A1MrKbjQaGGsGa0DtG0MYtDWIXAXSd+vAipsGEqlHHN1k13sSzG95Q0LUGg9ulJstThpqw9RBBGzf0CUeTTyryRSFT59TR9majUHbqsjfHCmLcDJdUuMBqUFhE0VwFGr0wOwZaXoVGrs4agMlnwxWzOlbuoUBNzPJtgvaJ5ebMAU1XK5vkggGmWe47CqJrkpprAYXj9Sc1NVFINGGFK0BNUI7qS6/oII4uiyU0kMSieBLrREHDSwWabDG8Mm+ghwha6laro5M1ApTipk1hHBMT1NZzkesQilMcyWtZ0QZQIE7UGVEB/ktsUTWQY5YoxfQave1xAopVQk6YFioxbaPtnvxImCl6HA3MVTkJmRA8hR33FKpduPDCzAnMURwvvTqZzhkzZ5umTwZY8owkZne2Vt7gDtAJKE4AQgZ5tZsOk9K41lqcAOEkQzgGEK4ZFzH/Edx8OgHFCkARU4y/U9ZgwgU42QeT+JWl4TCry62svC4XEoAdI5/m6lTH73CJOZXkKxhF6CSs5GN3EuJJqFFGHEuT0zpNytijKXMmGcxN7+V/Ql6To8xb6K03cVqQdv8mntpKz6P0Iw6uCY6tyI/DVzWNijaGTy0kArrjbXUgffIoouf1dqdyUlYyWkGx0iiBOhpbycqcHsHY7NgxIuG+o+4cRTwF1U1yDM2grDLGUjXuBSJT3cVwFY37NEdlwK07waakviETGyY/0eSL11DNTtHoio84FBr/gEcczB5/2z8OJk949IXvJpMdg4z4n7C4zJIUPhtLaPSeJw4ezLFljxAD4iCFSQwlvEOsyhXO4UZcSAMOA5am0TF9GdakN4aQq/GxETB7woiQyq3zL1ng/Pq0StHhVa6LjfpSfRm/CFSjazcZ2Dw3Y6yiFFZts0VlCueMkerp15SMfYKLVQbOT5L2BdfVFZVM0uzoT3kLcMg823JGx0tuv5rgTXpOpZCA7ZxAAywJ353EThO1kh/VSo34NQgDeherfqWB9qSBsj7QnzfQYk987SoBe/zj1cpmcErerN3DVrWBx9/DVvWAxzwyP5d4ZDdWSzpJx+XnYud2DU41T6dCpTSwtG1s/h4J4wsP2pOlEhIyt4TpZKSUnQ+tZOzdFSdyQkYCQ2an7KcTQQxTBUvnziQwZ0wdnU6oeI1ri9MJhW7SBYtpPZCqyj09Qnl7WlPX6oKR/rCn+LaQSU8Bx8HGtaQ40qTmFEc02irUKk5854n58Sad5mJoaKRGZTp3I1+L/Co7dQ2s8txSZbk+Vw7vyRNTpbfk6SnK8G3YGf/pxnDzGL/X4fFOBv+2XKcfimk2KvPkOweQmyw1KvBHxnIEESUgIoaIVIhIQmR38UUm6bujyUu21bwiA14FZJSOzHhGBjwLd/UFtqVXeUtv8tbIUDAQQh4KjTgUF6pgIBW9089ngb06XM29I3OfU3JPIVEyJOKQyBjSToa0OaRtDOkkQzoc0kmHDN4toLBp9k5ptVJtA4vg0MgIminXNrAA/sYAkXHyunWNDRiwK2KiBExuBAZ80uv/IpfkhYNqLl0DLkNElIDIeHQNeGQX+QUmFS+IV3OcNzGDEB+Z4jP+8wb8s+v6Iv/ie+fVnJu4NAEZpSMznk08GL5ML/LL3myv8b/TJuYbQKJkSO5npw24FG/ER8IHe1W+mmETfiPgKBWcsW7CuXjNPeIixPfxq7mfMeA+MgAyGoBJMGMgAb/ALpoJed1/imcOPH0K+yI6MkHniVLOxOuxO1Gi6uUvmUW/JaBL9Ew8ojAaGmc0LptJFhhWwXIGwr9eoJHEJA+UsFEqdpi8GvDN72KIbEe+kKBh3STWi/DICJ5zbxLv+f0KcTUIX2DQcG4S9kVolArNuTaJ/tGLEgLz+F2pT/8eftpBI4BJRqAYBRmNwmUxyRL4JQipRqOfkNBwb5IdiLgoGZfza5IVRN6KIYYvxbcpNAKYJAnxgZDxQFwik5wheAOGuADIxzA0rJuEYI6IEhA5j0YZQ/BCC9HQyec1NEyaRNoQEiVAci5NYmv4YgrJGQof7NDkYSahVQJH6eA8I8uZci6pV/lJEA37M6bsS9o2GIHLYKL98B0PUsUhfHVE10kxYF8CR+ngnHPLLB+mb0lQzUDwXRNNuZwzy4hDeGQCz0tmE9uRXoEgF/zSV1M0Epg4lOgQyGgILoWJh+H30KVMIPwgi8Z2TNIvERqlQodtOFPdxzyO+L0XDd+2qdZjHkcPzjk367REXhIh6j32NRmN7cwYtV/iAyHDgbgFzSj7coq5kG7tR79Go+khCSvAzeHv6xLwXAI4SgXnzSTB9rXg4d1Fqaal37fRNepMcmARGCUDc11bSl0ncGwnA9sc2B4R2EkGdjiwQT9UuoUo2jr74o+uwWiNjo2SsbltWAbdZukWn2zU/GtCGtZzpj5GvCSYCs+5F2ITJFBIOZ380p2ocfKpouSUwKTAE7FROjb3jiYVnnynTcwKlF880kyASXCKjYRGGClsWY8jkz3CSHw7A9mqkWzZqGKXyniNRj7bpFGXUUyMQaMEaK4fk4iovgqng+YKsQ0UIl4jE5ex8I2pTPCRKY1qHLPeHx8Eias5bRSuJWFlkE9CB6PgP8ruDt/TEteE8BErDf8mHQMGi1JhOcMmDQMGa6fC8inNG0wpuXglejXymS3xK1saVbgG2QYDR4bgXCEuMge3DcG5WlyD+C3cEeOaYR8D0yhkxkAhAixKhuWqmDEIT5EbbQmwXAkztkHU49d3clKzd/Cxq9kgzFnpqg1RrWRUvkmYM7CGEBUlo9oc1WBDW77AlIDqcFQnXa/y9Z7QvvAH2TLhF9k0e7DWqAMgowG4ti006gC20QBc8ZaB6Yk3PWQdxb8mp1EUskYeBpkPE+5gm6xPfolEPsegi5Ou0fEFARQlgHJObYM0XQS1E0D5ZKrTBj2okwDKF5HtmBwLCEHdBFCXg7rp0ZBdfIj2z9g3itSz5Sg9v6VDRqnIfMocs64fQ7ZTkfm8OUrvp9WGk4rMJ89xRG2wBeHokN1UZD6Djqtaaq4OOZ+KnOfIeVEbKG0GC6nIBY5cUPFckJDJRQapX3igdw3qLTdHCYgSALmNuQZ9EgZoJwBy03KVLsFVAjoJgNyiXMecQzcBkBuS66pMVA2YTwDk9uPm010rAywkAHKzcQvpUUV5/0M0I+FrnJr+hGvUWlEPg1KH4a0Kkw1cVZcivTeBTCoyVVsivRmBjLdx56K7XtIXQjV9T2S6dzsX3fFKQA/PKJoEDnorQ1Q4++iohmmTvESARcmwnFuTtga9HiFqOf7xUg3bJm2HEB+Z4nP+HbMDCnORDUX2KVQN167Z8YS5yE6iGpXz6przaqei8p64q8zpI60G4UZCvAksfqtVoxCTtR4ZBJkOwvVjsuqF2wbilMY/AasRxOTchjwGMh2Dy1EYWQ7bdAw+6wVNgwnfpSjdqDc+bZTYVYp5crdnsVLDl4XhD6U/BX8IBlxn328FU5vCLAb3Swh5jlLPcO7IFxVvH+DPIlJaRGktRmwx6qOdwccDRmZTMsTI0AxrHfcH3Q1G5lAym5HZfOyO39liZC4lcxiZw9DuH3mHLUaWp2QuI8N/IGj31v3n/eAoIP6aPVbbbGm5iT8zChrDFuGEMr/ugQ1PBbeHgqtSGL8SvEEh6H9hjeCU9L/plyk5qc1pEYt+296bg8FhJ0LocsICP6Y7vC2RFDiJGy4tYK67GcGCEMQoc+F9ANYbkCjDYafZCSvh6+WyJJw0zzandnC3r9UNyLCEkiDUxiBP91oSf/gi8Fd/+X+FWAv5HKUAAA==""")).decode('utf-8'))
S    = {int(k):v for k,v in DATA['status'].items()}
SK   = DATA['statKeyToId']
SCH  = DATA['schedule']
TH   = DATA['gradeThresholds']
ENDS = DATA['endings']
ESTAT= DATA['endingStatus']
REPG = DATA['reputation']
FLOW = sorted(DATA['flowEpisodes'], key=lambda x:x['so'])
LET  = {1:'D',2:'C',3:'B',4:'A',5:'S'}
TY   = {0:'무조건',1:'평판등급',2:'능력치',3:'능력치합',7:'소지금',8:'스케줄등급',9:'필드',10:'이벤트'}
CMP  = {0:'=',1:'≥',3:'≤'}

# ── 플로우 에피소드: 트리거 코드 의미 (전부 실플레이 검증) ──
TRIGN = {
    1010:('정기 자동',   '플레이어 선택과 무관하게 때가 되면 자동 발동. 배경이 집으로 바뀔 뿐 "휴식" 조건 아님'),
    1012:('편지 수령',   '편지가 도착할 때 자동'),
    1017:('스케줄 직후', '해당 스케줄(수업·알바·자유활동)을 수행한 직후에만 후보에 오름'),
    2012:('성 퀘스트 보고','성에서 퀘스트 완료를 보고하는 시점. 경쟁자 30개 — 대기 퀘스트를 비워야 차례가 옴'),
    5001:('축제 우승',   '축제에서 우승하는 시점 (축제 종료 전)'),
    5002:('수확제 연회', '수확제에서 연회에 참가할 때'),
}
# ── 실플레이로 확인된 발동 조건 ──
EPNOTE = {
 'Flow_Princess_Ep1':'린네 해금(예절 150) 상태에서 예술제 우승. 우승만으로는 안 됨',
 'Flow_Princess_Ep2':'Ep1 이후 자유활동',
 'Flow_Princess_Ep3':'성 NPC 9명 전원 실제 접견 (해금이 아니라 방문)',
 'Flow_Princess_Ep4':'편지 받은 뒤 수확제 연회 참가',
 'Flow_Princess_Ep5':'성에서 린네 재방문',
 'Flow_Princess_Ep6':'밀린 성 퀘스트를 전부 완료 → 대공의 편지 (스탯 게이트 아님)',
 'Flow_Princess_Ep7':'편지 받은 뒤 대공 접견. Pri 7이라 대기 퀘스트를 다 털어야 차례가 옴',
 'Flow_Queen_Ep1':'자유활동 — 마을 외곽 분쟁을 말로 중재',
 'Flow_Queen_Ep2':'자동 — 대공의 감사 편지',
 'Flow_Queen_Ep3':'자유활동 — 왕실 수레를 습격한 마수를 혼자 격퇴. 전투 스탯 필요',
 'Flow_Queen_Ep4':'자동 — 대공 친서(연회 초대장)',
 'Flow_Queen_Ep5':'수확제 연회 참가',
 'Flow_Queen_Ep6':'대공의 편지 — 여왕 엔딩 조건 7그룹을 전부 충족해야 온다 (실증 완료)',
 'Flow_Queen_Ep7':'편지 받은 뒤 성에서 대공 접견',
 'Flow_PrimaDonna_Ep1':'음악 수업 누적 22~25회',
 'Flow_PrimaDonna_Ep2':'음악 수업 누적 35~37회. 등급·스탯 무관, 순수 횟수',
}
# 여왕 Ep3 같은 전투 게이트를 눈으로 확인하기 위한 참고 스탯
FLOWSTAT = {'Flow_Queen_Ep3':['Strength','MotorAbility','FighterReputation','Attack']}
# 해당 엔딩의 조건을 전부 충족해야 열리는 에피소드
FLOWGATE = {'Flow_Queen_Ep6':'Ending_Queen'}
# 실플레이에서 관측한 발동/미발동 시점 — 임계값의 상한·하한
EPOBS = {
 'Flow_Queen_Ep3':'발동 확인: 힘 259·민첩 256·체력 382·전사평가 302 (14.9세, 자유활동 32회). '
                  '하한은 미상 — 이 수치면 확실히 뜬다는 뜻일 뿐',
 'Flow_PrimaDonna_Ep2':'발동 X: 음악 31·32·34회 / 발동 O: 37회',
 'Flow_Princess_Ep6':'발동 시점 기품+예절+화술 2374 — 엔딩 조건 2400 미만이므로 스탯 게이트 아님',
 'Flow_Queen_Ep6':'6/7 그룹(지마정 71 부족) → 안 옴 / 6/7 그룹(기예화 53 부족) → 안 옴 / '
                  '7/7 그룹 → 편지 도착. 하나라도 미달이면 안 온다',
}

def flow_chain(tkey):
    """엔딩 키에 딸린 플로우 에피소드 체인을 순서대로 반환."""
    grp = tkey[len('Ending_'):] if tkey.startswith('Ending_') else tkey
    pre = 'Flow_%s_'%grp
    return [e for e in FLOW if e['k'].startswith(pre)]

def rep_grade(v):
    for r in REPG:
        if r['min']<=v<=r['max']: return r['g']
    return 1
def has_grade(k):
    t=TH.get(k) or []
    return bool(t) and t[0] not in (None,0)
def sch_grade(k,pts):
    t=TH.get(k) or []
    g=1
    for i in range(4):
        if i<len(t) and t[i] is not None and pts>=t[i]: g=i+2
    return g

def eval_cond(r,ctx):
    t,tk,v,cp = r['t'], r['tk'], r['v'], r['c']
    if t==0: return dict(ok=True,cur='—',want='항상',gap=0,label='기본 조건')
    if t==2:
        i=SK.get(tk)
        if i is None: return dict(unk=True,label='능력치 '+tk)
        cur=ctx['stats'].get(i,0)
        okv = cur>=v if cp==1 else (cur==v if cp==0 else cur<=v)
        return dict(ok=okv,cur=cur,want=v,gap=(0 if okv or cp!=1 else v-cur),
                    label='%s %s %d'%(S.get(i,{}).get('n',tk),CMP.get(cp,'≥'),v))
    if t==3:
        names=[];cur=0
        for x in tk.split(','):
            i=SK.get(x); names.append(S.get(i,{}).get('n',x)); cur+=ctx['stats'].get(i,0)
        okv=cur>=v
        return dict(ok=okv,cur=cur,want=v,gap=0 if okv else v-cur,label='+'.join(names)+' ≥ %d'%v)
    if t==1:
        i=SK.get(tk)
        if i is None: return dict(unk=True,label='평판 '+tk)
        raw=ctx['stats'].get(i,0); g=rep_grade(raw)
        need=next((x['min'] for x in REPG if x['g']==v),0)
        okv=g>=v
        return dict(ok=okv,cur='%d등급(%d)'%(g,raw),want='%d등급(%d)'%(v,need),gap=0 if okv else need-raw,
                    label='%s %d등급 이상'%(S.get(i,{}).get('n',tk),v))
    if t==8:
        pts=ctx['pts'].get(tk,0); g=sch_grade(tk,pts)
        th=TH.get(tk) or []; need=th[v-2] if 0<=v-2<len(th) else None
        okv=g>=v
        return dict(ok=okv,cur='%s(%dpt)'%(LET[g],pts),want=LET.get(v,v),
                    gap=0 if okv or need is None else need-pts,
                    label='%s %s등급 이상'%(SCH.get(tk,{}).get('n',tk),LET.get(v,v)))
    if t==10:
        okv=tk in ctx['events']
        return dict(ok=okv,cur='봄' if okv else '못 봄',want='발생',gap=0,label='이벤트 '+tk)
    return dict(unk=True,label='%s 특수 조건'%(TY.get(t,'#%d'%t)))

def or_groups(rows):
    """OrGroup 단위로 묶는다. 같은 그룹 = OR 조건 — 하나만 충족해도 점수는 한 번만."""
    g={}
    for i,(r,e) in enumerate(rows):
        g.setdefault(r.get('g', -i-1), []).append((r,e))
    return g

def score(k,ctx):
    rows=[(r,eval_cond(r,ctx)) for r in ESTAT if r['k']==k]
    got=unk=mx=0
    for items in or_groups(rows).values():
        gs=max(r['s'] for r,e in items)
        mx+=gs
        if any(e.get('ok') and not e.get('unk') for r,e in items): got+=gs
        elif all(e.get('unk') for r,e in items): unk+=gs
    return rows,got,unk,mx

def groups_state(k,ctx):
    """OrGroup 단위 충족 현황 → (충족 수, 전체 수, 미충족 그룹 목록)."""
    rows=[(r,eval_cond(r,ctx)) for r in ESTAT if r['k']==k]
    done=0; miss=[]
    gs=or_groups(rows)
    for items in gs.values():
        if any(e.get('ok') and not e.get('unk') for r,e in items): done+=1
        elif all(e.get('unk') for r,e in items): done+=1      # 판정 불가 → 충족으로 간주
        else: miss.append(items)
    return done, len(gs), miss

def qualified(ctx):
    """자격을 갖춘 엔딩 = 모든 OrGroup을 충족한 엔딩.
    실측 57회 대조 결과, 엔딩은 '최고점'이 아니라 '전 조건 충족' 여부로 결정된다."""
    out=[]
    for k in ENDS:
        d,t,miss=groups_state(k,ctx)
        if not miss: out.append(k)
    return sorted(out, key=lambda k:(-ENDS[k]['w'], -score(k,ctx)[3]))

# ───────────────────────── 리포트 ─────────────────────────
def hr(t=''):
    line='─'*max(0,62-w(t))
    print('\n'+bold(t)+' '+dim(line) if t else dim('─'*64))

def report_flow(tkey, events, acct_seen, stats=None, ctx=None):
    """목표 엔딩의 플로우 에피소드 체인 — 이번 런 / 계정 / 조건."""
    chain = flow_chain(tkey)
    nm = ENDS.get(tkey,{}).get('n', tkey)
    if not chain:
        hr('플로우 에피소드 — %s'%nm)
        print('  '+dim('이 엔딩에는 플로우 에피소드가 없습니다.'))
        return
    run_got = [e for e in chain if e['k'] in events]
    acc_got = [e for e in chain if acct_seen and e['k'] in acct_seen]
    head = '플로우 에피소드 — %s   이번 회차 %d/%d' % (nm, len(run_got), len(chain))
    if acct_seen is not None:
        head += '   계정 %d/%d' % (len(acc_got), len(chain))
    hr(head)
    print('  '+dim('● 이번 회차에 봄   ◐ 계정엔 있음(과거 회차)   ○ 아직 못 봄'))
    print()
    for e in chain:
        k=e['k']
        inrun = k in events
        inacc = bool(acct_seen) and k in acct_seen
        if inrun:   mark, nmc = ok('●'), ok(pad(e['n'] or k, 22))
        elif inacc: mark, nmc = warn('◐'), pad(e['n'] or k, 22)
        else:       mark, nmc = bad('○'), bad(pad(e['n'] or k, 22))
        tn, td = TRIGN.get(e['trig'], ('트리거 %s'%e['trig'], ''))
        pri = e['pri']
        prim = ok('Pri %d'%pri) if pri==0 else (dim('Pri %d'%pri) if pri<=2 else warn('Pri %d'%pri))
        print('  %s %s %s  %s' % (mark, nmc, pad(tn,15), prim))
        note = EPNOTE.get(k)
        if note:
            print('      %s %s' % (dim('조건'), note if not inrun else dim(note)))
        else:
            print('      %s %s' % (dim('조건'), dim('미검증 — %s'%td)))
        if k in FLOWGATE and ctx:
            gk=FLOWGATE[k]
            gd,gt,gm=groups_state(gk,ctx)
            line='%s 조건 %d/%d 그룹 충족'%(ENDS.get(gk,{}).get('n',gk), gd, gt)
            if gm:
                line += ' — ' + ' / '.join(' 또는 '.join(e['label'] for r,e in it) for it in gm)
            print('      %s %s' % (dim('게이트'), (ok(line) if not gm else bad(line))))
        if k in EPOBS:
            print('      %s %s' % (dim('실측'), dim(EPOBS[k])))
        if not inrun and k in FLOWSTAT and stats:
            cur=', '.join('%s %s'%(S.get(SK.get(x),{}).get('n',x), stats.get(SK.get(x),0)) for x in FLOWSTAT[k])
            print('      %s %s' % (dim('참고'), dim('현재 '+cur)))
    nxt = next((e for e in chain if e['k'] not in events), None)
    print()
    if nxt is None:
        print('  '+ok('이번 회차에 체인을 전부 봤습니다. 🎉'))
    else:
        tn, td = TRIGN.get(nxt['trig'], ('트리거 %s'%nxt['trig'], ''))
        print('  %s %s' % (bold('다음 목표 →'), acc(nxt['n'] or nxt['k'])))
        print('  %s %s' % (dim('  발동 방식'), dim('%s · %s'%(tn, td))))
        if nxt['pri']>=3:
            print('  %s' % warn('  Priority %d — 같은 트리거의 Pri 0 이벤트가 대기 중이면 계속 밀립니다.'%nxt['pri']))

def report_castle(met, stats):
    """성 NPC 접견 현황 — 프린세스 Ep3·여왕 Ep6/7의 실질 게이트."""
    CAS = DATA.get('castle') or []
    if not CAS: return
    done=[x for x in CAS if x['i'] in met]
    hr('성 접견  %s' % dim('%d/%d명'%(len(done),len(CAS))))
    print('  '+dim(pad('NPC',14)+pad('해금 조건',18)+pad('상태',10)+'방문'))
    for x in sorted(CAS, key=lambda y:y['v']):
        sname=S.get(x['s'],{}).get('n','능력치 %d'%x['s'])
        cur=stats.get(x['s'],0)
        unlocked = cur>=x['v']
        v=met.get(x['i'])
        n=v[0] if isinstance(v,list) and v else (v or 0)
        if n:      state=ok('접견함')
        elif unlocked: state=warn('미접견')
        else:      state=bad('잠김')
        need='%s %d'%(sname,x['v']) if x['v'] else '없음'
        print('  %s%s%s%s'%(pad(x['n'],14), pad(need,18), pad(state,10),
              dim('%d회'%n) if n else dim('—')))
    todo=[x['n'] for x in CAS if x['i'] not in met and stats.get(x['s'],0)>=x['v']]
    if todo:
        print()
        print('  %s %s' % (warn('아직 안 만난 사람'), ', '.join(todo)))
        print('  ' + dim('성 퀘스트는 접견한 NPC가 준다. 편지가 안 오면 여기부터 확인.'))

def find_saves():
    """세이브 폴더를 찾습니다. 폴더 이름이 곧 Steam64 ID입니다."""
    base=os.path.join(os.path.expanduser('~'),'AppData','LocalLow','GEAR2','PrincessMakerKaren','Save')
    found=[]
    for d in sorted(glob.glob(os.path.join(base,'*'))):
        files=glob.glob(os.path.join(d,'*.sav'))
        if files:
            found.append((d, files, os.path.basename(d.rstrip(os.sep))))
    if not found: return None, [], None
    found.sort(key=lambda x: max(os.path.getmtime(f) for f in x[1]), reverse=True)
    return found[0]

def report_slot(o, target_name, acct_seen=None, flow_only=False):
    stats={int(k):v for k,v in o[26].items()}
    pts={}; cnt={}
    for k,v in o[27].items(): cnt[k]=v[1]; pts[k]=v[2]
    events=set(o[31].keys()) if isinstance(o[31],dict) else set(o[31])
    ctx=dict(stats=stats,pts=pts,events=events)

    born=o[8].get('__ts') if isinstance(o[8],dict) else None
    now =o[34].get('__ts') if isinstance(o[34],dict) else None
    turns=sum(len(v[4]) for v in o[27].values() if len(v)>4 and isinstance(v[4],list))

    hr('현재 상태')
    if now:
        d=datetime.datetime(1970,1,1)+datetime.timedelta(seconds=now)
        age=10+(now-born)/86400/365.25 if born else None
        print('  게임 날짜 %s      딸 나이 %s세      사용 턴 %s' % (
            bold('%d년 %d월 %d일'%(d.year,d.month,d.day)),
            bold('%.2f'%age) if age else '—', bold(turns)))
    print('  기력 %s / 1000      성향 %s / 300' % (bold(stats.get(15,'—')), bold(stats.get(13,'—'))))

    ranked=sorted(((k,)+score(k,ctx) for k in ENDS), key=lambda x:(-x[2], -ENDS[x[0]]['w']))
    tkey=None
    for k,v in ENDS.items():
        if v['n']==target_name or k==target_name: tkey=k; break
    if tkey is None: tkey=ranked[0][0]

    met = o[46] if len(o)>46 and isinstance(o[46],dict) else {}

    if flow_only:
        report_flow(tkey, events, acct_seen, stats, ctx)
        report_castle(met, stats)
        return

    rows,got,unk,mx = score(tkey,ctx)
    done,total,miss = groups_state(tkey,ctx)
    qual = qualified(ctx)

    print()
    if qual:
        wk=qual[0]
        if wk==tkey:
            print('  ' + ok(bold('지금 끝나면 → %s 엔딩'%ENDS[wk]['n'])))
        else:
            print('  ' + bad(bold('지금 끝나면 → %s 엔딩'%ENDS[wk]['n'])) +
                  dim('   (자격 %d개 중 Weight 최상위 · 예측 적중률 81%%)'%len(qual)))
    else:
        print('  ' + bad(bold('지금 끝나면 → 자격을 갖춘 엔딩이 없습니다')))

    hr('목표 엔딩 — %s' % ENDS[tkey]['n'])
    barlen=40; fill=int(done/total*barlen) if total else 0
    okmark = ok('자격 있음 ✓') if not miss else bad('%d개 조건 미달'%len(miss))
    print('  조건 %s / %d 그룹 충족   %s   %s' % (
          acc(bold('%d'%done)), total, okmark, dim('Weight %d'%ENDS[tkey]['w'])))
    print('  [' + (ok if not miss else acc)('█'*fill) + dim('░'*(barlen-fill)) + ']')
    if miss:
        near=[]
        for items in miss:
            g=min((e.get('gap') or 0) for r,e in items if not e.get('unk')) if any(not e.get('unk') for r,e in items) else 0
            lbl=' 또는 '.join(e['label'] for r,e in items)
            near.append((g,lbl))
        near.sort()
        print('  ' + bad('남은 조건:'))
        for g,lbl in near:
            print('    %s %s' % (bad('✗'), lbl + (dim('   %d 부족'%g) if g else '')))
    else:
        print('  ' + ok('이 엔딩의 조건은 전부 충족했습니다.'))
    print()
    print('  ' + dim('※ 엔딩은 점수 합계가 아니라 조건 전부 충족 여부로 결정됩니다 (실측 57회 대조).'))
    print('  ' + dim('   아래 배점은 참고용 — 하나라도 미달이면 자격이 없습니다.'))
    print()
    print('  ' + dim(pad('조건',34)+pad('배점',5,True)+'  '+pad('현재',14)+pad('목표',14)+'부족'))
    groups=sorted(or_groups(rows).values(), key=lambda it:-max(r['s'] for r,e in it))
    for items in groups:
        gs=max(r['s'] for r,e in items)
        gok=any(e.get('ok') and not e.get('unk') for r,e in items)
        # 배점은 '그룹을 대표하는 줄'에만 적는다 — 충족됐으면 충족한 줄에
        anchor=next((i for i,(r,e) in enumerate(items)
                     if e.get('ok') and not e.get('unk')), 0) if gok else 0
        for j,(r,e) in enumerate(items):
            # OR 그룹이 이미 다른 줄로 충족됐다면, 이 줄은 안 해도 되는 조건이다
            moot = gok and len(items)>1 and not (e.get('ok') and not e.get('unk'))
            if moot:
                mark=dim('·'); gaps=dim('불필요')
                cell=lambda s,n,right=False: strike(pad(s,n,right))
            else:
                if e.get('unk'): mark=warn('?'); gaps=dim('미확인')
                elif e['ok']:    mark=ok('✓');   gaps=dim('—')
                else:            mark=bad('✗');  gaps=bad(str(e['gap'])) if e.get('gap') else bad('미달')
                cell=lambda s,n,right=False: pad(s,n,right)
            sc = cell(gs,5,True) if (len(items)==1 or j==anchor) else dim(pad('또는',5,True))
            print('  %s %s%s  %s%s%s' % (mark, cell(e['label'],32), sc,
                  cell(e.get('cur','—'),14), cell(e.get('want','—'),14), gaps))
        if len(items)>1:
            if gok:
                print('    %s' % dim('↑ %s 충족 — 나머지는 채워도 점수가 늘지 않는다.'%ok('이미')))
            else:
                print('    %s' % dim('↑ 둘 중 %s 충족하면 %d점. 둘 다 채워도 점수는 그대로다.'%(bold('하나만'),gs)))

    report_flow(tkey, events, acct_seen, stats, ctx)
    report_castle(met, stats)

    hr('자격을 갖춘 엔딩  %s' % dim('%d개 · Weight 높은 순'%len(qual)))
    if not qual:
        print('  '+dim('아직 없습니다.'))
    for i,k in enumerate(qual[:12],1):
        crown=' 🏆' if i==1 else '   '
        line='  %s %s%s %s' % (dim(pad(i,2,True)), pad(ENDS[k]['n'],16), crown,
                               dim('Weight %d'%ENDS[k]['w']))
        print(acc(line) if k==tkey else line)

    # ── 자격까지 조건 1~2개 남은 엔딩 ──
    close=[]
    for k in ENDS:
        if k in qual or k==tkey: continue
        d,t,ms=groups_state(k,ctx)
        if 0<len(ms)<=2: close.append((len(ms),k,ms))
    close.sort(key=lambda x:(x[0],-ENDS[x[1]]['w']))
    if close:
        hr('자격에 근접한 엔딩  %s' % dim('한 끗 차이로 끼어들 수 있는 것들'))
        for n,k,ms in close[:6]:
            print('  %s %s' % (pad(ENDS[k]['n'],16), dim('조건 %d개 남음 · Weight %d'%(n,ENDS[k]['w']))))
            for items in ms:
                lbl=' 또는 '.join(e['label'] for r,e in items)
                g=min((e.get('gap') or 0) for r,e in items if not e.get('unk')) if any(not e.get('unk') for r,e in items) else 0
                print('    %s %s'%(dim('·'), dim(lbl + ('   %d 부족'%g if g else ''))))

    # ── 자격을 뺏길 위험 ──
    if tkey in qual:
        rivals=[k for k in qual if k!=tkey and ENDS[k]['w']>ENDS[tkey]['w']]
        hr('자격 경쟁  %s' % dim('나보다 Weight가 높은데 자격까지 갖춘 엔딩'))
        if not rivals:
            print('  '+ok('없습니다 — 지금 끝나면 목표 엔딩이 나옵니다.'))
        else:
            for k in rivals:
                print('  %s %s' % (bad(pad(ENDS[k]['n'],16)), dim('Weight %d > %d'%(ENDS[k]['w'],ENDS[tkey]['w']))))
            print('  '+dim('이 엔딩들의 조건 중 하나를 일부러 미달로 두면 목표가 우선합니다.'))

    hr('스케줄 등급')
    order=sorted((k for k in pts if k in SCH), key=lambda k:-pts[k])
    print('  '+dim(pad('스케줄',14)+pad('횟수',6,True)+pad('점수',8,True)+pad('등급',6,True)+'  다음 등급까지'))
    for k in order:
        if pts[k]==0 and cnt[k]==0: continue
        nm=SCH[k]['n'] or k.replace('Festival_','축제·')
        if not has_grade(k):
            print('  %s%s%s%s  %s'%(pad(nm,14),pad(cnt[k],6,True),pad(pts[k],8,True),pad('—',6,True),dim('등급 없음')))
            continue
        g=sch_grade(k,pts[k]); th=TH.get(k) or []
        nxt=th[g-1] if g-1<len(th) and th[g-1] is not None else None
        rest=('%dpt (%d회)'%(nxt-pts[k], -(-(nxt-pts[k])//10))) if nxt else dim('최고 등급 S')
        print('  %s%s%s%s  %s'%(pad(nm,14),pad(cnt[k],6,True),pad(pts[k],8,True),pad(LET[g],6,True),rest))

    seen=[e for e in FLOW if e['k'] in events]
    hr('이번 회차 플로우 에피소드  (%d개)'%len(seen))
    for e in seen:
        print('  %s %s %s'%(ok('●'), pad(e['n'] or e['k'],26), dim('T%s·P%s'%(e['trig'],e['pri']))))

def report_account(a):
    seen=set(a.get('EventKeys') or [])
    miss=[e for e in FLOW if e['k'] not in seen]
    got=[k for k in ENDS if k in set(a.get('EndingList') or [])]
    hr('계정 진행도')
    print('  획득 엔딩 %s / %d      엔딩 횟수 %s' % (bold(len(got)), len(ENDS), bold(a.get('EndingCount',0))))
    print('  플로우 에피소드 %s / %d' % (bold(len(FLOW)-len(miss)), len(FLOW)))
    print('  질서 %s   혼돈 %s' % (bold(a.get('LawfulPoint',0)), bold(a.get('ChaoticPoint',0))))
    hr('미획득 플로우 에피소드  (%d개)'%len(miss))
    if not miss: print('  '+ok('전부 획득했습니다.'))
    for e in miss:
        print('  %s %s %s'%(bad('○'), pad(e['n'] or e['k'],26), dim('T%s·P%s'%(e['trig'],e['pri']))))
    missend=[k for k in ENDS if k not in got]
    hr('미획득 엔딩  (%d개)'%len(missend))
    if not missend: print('  '+ok('전부 획득했습니다.'))
    for k in missend:
        print('  %s %s %s'%(bad('○'), pad(ENDS[k]['n'],16), dim(ENDS[k].get('hint') or '')))

def clear_screen():
    try: os.system('cls' if os.name=='nt' else 'clear')
    except Exception: print('\n'*3)

def mtime(f):
    try: return os.path.getmtime(f)
    except OSError: return None

def wait_next(pick_fn, cur_mt):
    """파일이 바뀌거나 키를 누를 때까지 대기. 'q'면 None 반환."""
    import time
    print()
    print(dim('  ─ 세이브가 갱신되면 자동으로 다시 분석합니다.   [아무 키] 지금 새로고침   [Q] 종료 ─'))
    if os.name=='nt':
        try:
            import msvcrt
        except ImportError:
            msvcrt=None
        if msvcrt:
            while True:
                if msvcrt.kbhit():
                    ch=msvcrt.getch()
                    if ch in (b'q',b'Q'): return None
                    return True
                f=pick_fn()
                if f and mtime(f)!=cur_mt: 
                    time.sleep(0.4)   # 저장이 끝날 때까지 살짝 대기
                    return True
                time.sleep(1.0)
    try:
        v=input('  > ').strip().lower()
    except (EOFError,KeyboardInterrupt):
        return None
    return None if v=='q' else True

def main():
    args=[a for a in sys.argv[1:]]
    target='여왕'
    if '--target' in args:
        i=args.index('--target'); target=args[i+1]; del args[i:i+2]
    sid=None
    if '--steamid' in args:
        i=args.index('--steamid'); sid=args[i+1]; del args[i:i+2]
    d, files, folder_sid = find_saves()
    if sid is None: sid=folder_sid
    if not d:
        print(bad('세이브 폴더를 찾지 못했습니다.'))
        print(dim('  기대 경로: %USERPROFILE%\\AppData\\LocalLow\\GEAR2\\PrincessMakerKaren\\Save\\<steamID>'))
        sys.exit(1)
    files.sort(key=lambda f:os.path.getmtime(f), reverse=True)
    if '--endings' in args:
        hr('엔딩 이름 목록')
        names=sorted(v['n'] for v in ENDS.values())
        for i in range(0,len(names),4):
            print('  '+''.join(pad(x,17) for x in names[i:i+4]))
        return
    if not (sid and sid.isdigit() and len(sid)==17):
        print(bad('Steam64 ID를 알 수 없습니다: %r'%sid))
        print(dim('  세이브 폴더 이름이 17자리 숫자여야 합니다. 직접 지정하려면:'))
        print(dim('    run.bat --steamid 7656119xxxxxxxxxx'))
        sys.exit(1)
    if '--list' in args:
        hr('세이브 목록  %s'%dim(d))
        for f in files:
            t=datetime.datetime.fromtimestamp(os.path.getmtime(f)).strftime('%m/%d %H:%M')
            print('  %s %s %s'%(pad(os.path.basename(f),20), dim(t), dim('%,d bytes'.replace(',','')%os.path.getsize(f))))
        return
    pick=None
    for a in args:
        if a.startswith('--'): continue
        for f in files:
            if a.lower() in os.path.basename(f).lower(): pick=f; break
        if pick: break
    if pick is None:
        pick=next((f for f in files if os.path.basename(f).startswith('slot_')), files[0])
    def wrongkey():
        print(bad('복호화에 실패했습니다 — Steam64 ID가 맞지 않는 것 같습니다.'))
        print(dim('  현재 사용한 ID: %s'%sid))
        print(dim('  세이브 폴더 이름이 곧 Steam64 ID입니다. 직접 지정하려면:'))
        print(dim('    run.bat --steamid 7656119xxxxxxxxxx'))
    explicit = any(not a.startswith('--') for a in args)
    once = ('--once' in args)
    flow_only = ('--flow' in args)

    def load_acct():
        """계정 파일에서 '과거 회차에 본 에피소드' 목록을 읽습니다. 실패해도 무시."""
        p=os.path.join(d,'account.sav')
        if not os.path.exists(p): return None
        try:
            a=load_sav(p, sid)
            return set(a.get('EventKeys') or [])
        except Exception:
            return None

    def repick():
        fs=glob.glob(os.path.join(d,'*.sav'))
        if not fs: return None
        fs.sort(key=lambda f: os.path.getmtime(f), reverse=True)
        return next((f for f in fs if os.path.basename(f).startswith('slot_')), fs[0])

    first=True
    while True:
        if not first and not explicit:
            np=repick()
            if np: pick=np
        if not first: clear_screen()
        first=False
        print(dim('  ← %s  (%s)   Steam ID %s'%(os.path.basename(pick),
              datetime.datetime.fromtimestamp(os.path.getmtime(pick)).strftime('%Y-%m-%d %H:%M'), sid)))
        try:
            o=load_sav(pick, sid)
        except Exception:
            wrongkey(); sys.exit(1)
        if isinstance(o,list) and len(o)>50: report_slot(o,target,load_acct(),flow_only)
        elif isinstance(o,dict) and 'EventKeys' in o: report_account(o)
        else: wrongkey(); sys.exit(1)
        if once: break
        if wait_next(repick if not explicit else (lambda: pick), mtime(pick)) is None: break
    print()

if __name__=='__main__':
    main()
