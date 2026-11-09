"""Independent bitboard replay of the merged both-player local rule.
P is the controlled player's bitboard, Q the other player's; all coordinates in code
are zero-based. No imports from the author implementation or earlier solver.
"""
import sys,json
from functools import lru_cache

def verify(H,first):
 assert H>=0
 if H==0:return dict(height=0,side="first" if first else "second",states=0,opponent_edges=0,max_active=0,max_off=0,draws=1)
 lines=[];nv=[];base=[]
 for c in range(4):
  for r in range(H):
   for dc,dr in [(1,0),(0,1),(1,1),(1,-1)]:
    pts=[(c+i*dc,r+i*dr)for i in range(4)]
    if all(0<=x<4 and 0<=y<H for x,y in pts):
     L=sum(1<<(x*H+y)for x,y in pts);lines.append(L)
     if dc:
      nv.append(L)
      if any(y==0 for x,y in pts):base.append(L)
 bycell=[[L for L in lines if L&(1<<i)]for i in range(4*H)]
 bottom=sum(1<<(j*H)for j in range(4))
 cmask=[((1<<H)-1)<<(j*H)for j in range(4)]
 alternating_P=[sum(1<<r for r in range(1,n,2))for n in range(H+1)]
 alternating_Q=[sum(1<<r for r in range(0,n,2))for n in range(H+1)]
 def won(bits,i):return any(bits&L==L for L in bycell[i])
 def board(h,P,Q):
  return tuple(''.join('P'if P&(1<<(j*H+r))else'Q'for r in range(h[j]))for j in range(4))
 @lru_cache(None)
 def cert(h,P,Q):
  R=tuple(j for j,n in enumerate(h)if (H-n)%2)
  E=0
  for j,n in enumerate(h):
   col=(Q>>(j*H))&((1<<n)-1)
   E|=(col&(col<<1))<<(j*H)
   if n<H and n and col&(1<<(n-1)):
    run=0
    for r in range(n-1,-1,-1):
     if col&(1<<r):run+=1
     else:break
    if run>2:return None
    E|=1<<(j*H+n)
  U=[L for L in nv if L&(E|bottom) and not L&P]
  if not U:return ('permanent',)
  for j,n in enumerate(h):
   if sum(H-h[k]for k in range(4)if k!=j)%2:continue
   for g in range(n+2,H+1,2):
    bit=1<<(j*H+g-1)
    if all(L&bit for L in U):return ('block',j,g)
  for j,n in enumerate(h):
   if sum(H-h[k]for k in range(4)if k!=j)%2:continue
   for g in range(n+2,H+1,2):
    idx=j*H+g-1;upper=((1<<(H-g+1))-1)<<idx
    if all(L&upper for L in U)and won(P|(1<<idx),idx):return ('win',j,g)
  if len(R)==4 and h[1]==h[2]==0 and (h[0]or h[3]) and all(h[j]%2==0 and (P&cmask[j])>>(j*H)==alternating_P[h[j]] and (Q&cmask[j])>>(j*H)==alternating_Q[h[j]] for j in (0,3)):
   return ('wait',)
  if len(R)not in(0,2):return None
  G=P
  for j,n in enumerate(h):
   G|=sum(1<<(j*H+r)for r in range(n+1,H,2))
  if any(not L&G for L in U):return None
  if len(R)==2:
   for r in R:
    shifted=(G&~cmask[r])|(1<<(r*H+H-1))
    if any(not L&shifted for L in U):return None
  return ('pair',R)
 st=dict(height=H,side='first'if first else'second',states=0,opponent_edges=0,own_wins=0,draws=0,uncovered_states=0,fallback_responses=0)
 def check_shape(h,P,Q):
  assert H>=4 and H%2==0
  b=board(h,P,Q);corners=bool(P&1 and P&(1<<(3*H)))
  if not corners:
   a=(h[0]-1)//2;d=h[3]//2
   assert b==('P'+'QP'*a,'','','QP'*d)and(a==0 or d>=1),(H,b)
  else:
   a=(h[0]-2)//2;bpar=h[1]//2;c=h[2]//2;d=(h[3]-1)//2
   assert b==('PQ'+'QP'*a,'QP'*bpar,'QP'*c,'P'+'QP'*d),(H,b)
 @lru_cache(None)
 def visit(h,P,Q):
  st['states']+=1
  assert sum(h)%2==int(first)
  before=cert(h,P,Q)
  R=tuple(j for j,n in enumerate(h)if (H-n)%2)
  if before is None:
   st['uncovered_states']+=1
   if first:check_shape(h,P,Q)
   else:assert h==(0,0,0,0)
  elif first:assert before[0]not in('pair','wait')
  elif before[0]=='wait':assert len(R)==4
  else:assert len(R)in(0,2),('unexpected four odd columns after certificate',H,board(h,P,Q),before)
  ma=mt=0
  for q,n in enumerate(h):
   if n==H:continue
   st['opponent_edges']+=1;qi=q*H+n;QQ=Q|(1<<qi)
   assert not won(QQ,qi),('opponent first win',H,board(h,P,Q),q,before)
   hq=list(h);hq[q]+=1
   if sum(hq)==4*H:st['draws']+=1;continue
   legal=[p for p in range(4)if hq[p]<H]
   choices={};wins=[];safe=[]
   for p in legal:
    pi=p*H+hq[p];PP=P|(1<<pi);hp=hq.copy();hp[p]+=1
    w=won(PP,pi);after=None if w else cert(tuple(hp),PP,QQ)
    choices[p]=(tuple(hp),PP,w,after)
    if w:wins.append(p)
    elif after:safe.append(p)
   good=set(safe+wins);filled=hq[q]==H
   corners=bool(P&1 and P&(1<<(3*H)))
   if before and before[0]!='wait':
    if not filled:assert q in good,('cover closure fails',H,board(h,P,Q),q)
    else:
     assert good,('full column closure fails',H,board(h,P,Q),q)
     if not first:
      assert len(R)==2 and q in R
      other=next(r for r in R if r!=q)
      assert other in good,('other odd column unsafe',H,board(h,P,Q),q,before)
   if before and before[0]=='wait':
    assert not corners and good
    if q in(0,3)and not filled:assert q in good
   if not filled and(q in good or corners):p=q
   elif good:
    odd=[p for p in safe if(H-hq[p])%2]
    p=min(wins)if wins else min(odd or safe)
   else:
    assert first and before is None and not filled
    st['fallback_responses']+=1
    if hq[q]>=3:p=q
    else:
     scores={p:sum(bool(L&choices[p][1])for L in base)for p in legal}
     top=max(scores.values());p=q if scores[q]==top else min(p for p in legal if scores[p]==top)
   hp,PP,w,after=choices[p]
   active=int(p!=q and not filled);off=int(p!=q)
   if before and before[0]!='wait':
    assert not active
    assert w or after is not None
    if not first and filled and not w:
     assert all((H-n)%2==0 for n in hp),('post-switch R not empty',H,board(h,P,Q),q,p,after)
   if before and before[0]=='wait'and(q in(1,2)or filled)and not w:
    assert after is not None and after[0]!='wait'
   if w:st['own_wins']+=1;ca=ct=0
   elif sum(hp)==4*H:st['draws']+=1;ca=ct=0
   else:ca,ct=visit(hp,PP,QQ)
   ma=max(ma,active+ca);mt=max(mt,off+ct)
  return ma,mt
 st['max_active'],st['max_off']=visit((1,0,0,0),1,0)if first else visit((0,0,0,0),0,0)
 assert st['max_active']<=1 and st['max_off']<=(4 if first else 2)
 if not first:assert st['fallback_responses']==0 and st['uncovered_states']==1
 if first and(H<=3 or H%2):assert st['uncovered_states']==0 and st['max_active']==0
 st['certificate_cache']=cert.cache_info().currsize
 return st
if __name__=='__main__':
 for H in map(int,sys.argv[1:]):
  for first in(True,False):print(json.dumps(verify(H,first)),flush=True)
