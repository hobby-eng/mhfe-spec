from itertools import product, permutations
from collections import Counter
from fractions import Fraction as F
import hashlib, json, math, sys
out={}
# G1: two entropy bits? Here 1 entropy bit and 1 verifier bit; G has one extra unprogrammed bit.
checks=0
for perm in permutations(range(4)):
    real=Counter(); planted=Counter()
    for g in product(range(4), repeat=2):
        for e in range(2):
            real[(perm[2*e+(g[e]//2)],g)]+=1
        for y in range(4):
            x=perm.index(y); e,v=divmod(x,2)
            gp=list(g); gp[e]=2*v+(gp[e]%2)
            planted[(y,tuple(gp))]+=1
    assert {key:2*val for key,val in real.items()}==planted
    checks+=len(planted)
out["G1_joint_cells"]=checks
# K1: four one-bit-half rounds; preserve all six unprogrammed H bits.
checks=0
for x in range(4):
    for j in range(3):
        real=Counter(); planted=Counter()
        for h in product(range(2),repeat=8):
            l,r=divmod(x,2)
            for i in range(4): l,r=r,l^h[2*i+r]
            real[(2*l+r,h)]+=1
            for y in range(4):
                lf,rf=divmod(x,2)
                for i in range(j): lf,rf=rf,lf^h[2*i+rf]
                lb,rb=divmod(y,2)
                for i in range(3,j+1,-1): lb,rb=rb^h[2*i+lb],lb
                hp=list(h)
                hp[2*j+rf]=lb^lf
                hp[2*(j+1)+lb]=rb^rf
                planted[(y,tuple(hp))]+=1
        assert {key:4*val for key,val in real.items()}==planted
        checks+=len(planted)
out["K1_joint_cells"]=checks
checks=0
for f,b in product(range(13),repeat=2):
    forward=set(range(f)); backward=set(range(12-b,12))
    bad={j for j in range(11) if j in forward or j+1 in backward}
    assert len(bad)<=min(11,len(forward|backward))
    checks+=1
out["K4_prefix_suffix_cases"]=checks
checks=0
for p in [(5,3,1,1),(4,4,2,0),(10,0,0,0)]:
    best=[F(0) for _ in range(45)]
    for weights in product(range(12),repeat=4):
        score=sum(F(a*u,110) for a,u in zip(p,weights))
        best[sum(weights)]=max(best[sum(weights)],score)
        checks+=1
    for budget in range(45):
        greedy=sum(F(p[i]*min(11,max(0,budget-11*i)),110) for i in range(4))
        assert max(best[:budget+1])==greedy
out["fractional_top_weight_vectors"]=checks
p=[F(5,10),F(3,10),F(1,10),F(1,10)]
s=[F(5,10),F(3,10),F(2,10)]
pairs=list(product(range(4),range(3)))
checks=0
for bits in product(range(2),repeat=12):
    chosen=[ij for ij,bit in zip(pairs,bits) if bit]
    m=len({i for i,j in chosen}); n=len(chosen)
    value=sum((p[i]*s[j] for i,j in chosen),F(0))
    cap=sum(sorted((p[i]*s[j] for i in range(m) for j in range(3)),reverse=True)[:n],F(0))
    assert value<=cap
    checks+=1
out["W1_pair_sets"]=checks
checks=0
for bits in product(range(2),repeat=12):
    chosen=[ij for ij,bit in zip(pairs,bits) if bit]
    prob=sum((s[j]/4 for i,j in chosen),F(0))
    assert prob<=s[0]*len(chosen)/4
    checks+=1
out["s1_fixed_query_sets"]=checks
# W2: enumerate finite S:E(2)->seed(4), T:seed(4)->bit, trials capped at 3.
# Re-randomize every distinct rejected S and T input; retain only terminating paths.
erased=Counter(); terminating_weight=0
for sv in product(range(4),repeat=2):
    for tv in product(range(2),repeat=4):
        for trials in product(range(2),repeat=3):
            accepted=next((j for j,e in enumerate(trials) if tv[sv[e]]==0),None)
            if accepted is None: continue
            e=trials[accepted]; d=sv[e]
            rejected_e=sorted(set(trials[:accepted]))
            rejected_d=sorted({sv[t] for t in rejected_e})
            choices=list(product(range(4),repeat=len(rejected_e)))
            tchoices=list(product(range(2),repeat=len(rejected_d)))
            denom=len(choices)*len(tchoices)
            assert 8%denom==0
            for se in choices:
                for td in tchoices:
                    sf=list(sv); tf=list(tv)
                    for idx,val in zip(rejected_e,se): sf[idx]=val
                    for idx,val in zip(rejected_d,td): tf[idx]=val
                    erased[(e,d,tuple(sf),tuple(tf))]+=8//denom
            terminating_weight+=8
assert len(erased)==256
assert len(set(erased.values()))==1
assert sum(erased.values())==terminating_weight
out["W2_erased_joint_cells"]=len(erased)
out["W2_termination_probability"]=str(F(terminating_weight,16*16*8*8))
# Selection conditioned on a success: first/last are uniform; minimum value is not.
selection={}
for rule in ("first","last","minimum"):
    counts=Counter()
    for trials in product(range(4),repeat=4):
        hits=[e for e in trials if e in (1,3)]
        if not hits: continue
        selected=hits[0] if rule=="first" else hits[-1] if rule=="last" else min(hits)
        counts[selected]+=1
    if rule!="minimum": assert counts[1]==counts[3]
    else: assert counts[1]>counts[3]
    selection[rule]=dict(counts)
out["selection_counts"]=selection
N=2**20; fp=2**-16
out["W7_check_only_success"]={str(n): -math.expm1(n*math.log1p(-fp))/(N*fp) for n in (2**18,2**19,2**20)}
out["constant_sums"]={"G3":sum(range(12)),"K3":66+144+66+11,"Ktotal":66+144+66+11+132}
print(json.dumps(out,sort_keys=True,indent=2))
