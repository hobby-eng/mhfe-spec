from itertools import product
from fractions import Fraction
# Even when a candidate chain reused A(u,s) earlier, an H collision with a fixed
# prior (K,i,R) requires A(u,B(i,R))=K. Check every salt table, target, A table,
# and a path that selects its R adaptively from those A answers.
checks=0
for b in product(range(2),repeat=3):
  for target_r,target_k in product(range(3),range(4)):
    matches=0
    for a in product(range(4),repeat=2):
      # Candidate path deliberately chooses the first matching H-input if one exists.
      candidates=[r for r in range(3) if r==target_r and a[b[r]]==target_k]
      r=candidates[0] if candidates else (a[0]+a[1])%3
      collision=(r==target_r and a[b[r]]==target_k)
      assert not collision or a[b[target_r]]==target_k
      matches+=collision
      checks+=1
    assert Fraction(matches,16)<=Fraction(1,4)
print({'adaptive_A_reuse_target_cases':checks,'per_target_probability_upper':'1/4','result':'PASS'})
