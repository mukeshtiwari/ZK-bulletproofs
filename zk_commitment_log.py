from py_ecc.bn128 import G1, multiply, add, FQ, eq, Z1
from py_ecc.bn128 import curve_order as p
import numpy as np
from functools import reduce
import random

def random_element():
  return random.randint(0, p)

def add_points(*points):
  return reduce(add, points, Z1)


# return (L, R)
def compute_secondary_diagonal(G_vec, a):
    n = len(a)
    L = add_points(*[multiply(G_vec[i+1], a[i]) for i in range(0, n, 2)])
    R = add_points(*[multiply(G_vec[i], a[i+1]) for i in range(0, n, 2)])
    return L, R

def compute_secondary_diagonal_scalor(a, b):
    n = len(a)
    L = reduce(lambda x, y: (x + y) % p, [b[i+1] * a[i] for i in range(0, n, 2)], 0)
    R = reduce(lambda x, y: (x + y) % p, [b[i] * a[i+1] for i in range(0, n, 2)], 0)
    return L, R

# return a folded vector of length n/2 for points
def fold_points(point_vec, u):
    n = len(point_vec)
    uinv = pow(u, -1, p)
    assert 2 <= n, "n must be at least 2"
    assert n % 2 == 0, "n must be even"
    return [(add_points(multiply(point_vec[i], u), multiply(point_vec[i + 1], uinv))) for i in range(0, n, 2)]


def fold_scalor(scalar_vec, u):
  n = len(scalar_vec)
  uinv = pow(u, -1, p)
  assert 2 <= n, "n must be at least 2"
  assert n % 2 == 0, "n must be even"
  return [(scalar_vec[i] * u + scalar_vec[i + 1] * uinv) % p for i in range(0, n, 2)]


def commitment_proof_log(P, G, H, Q, a, b):
  n = len(a)
  if n == 1:
    return (P, G, H, Q, a, b)
  else:
    La, Ra = compute_secondary_diagonal(G, a)
    Lb, Rb = compute_secondary_diagonal(H, b)
    Lc, Rc = compute_secondary_diagonal_scalor(a, b)

    L = add_points(multiply(Q, Lc), La, Rb)
    R = add_points(multiply(Q, Rc), Ra, Lb)

    u = random_element()

    Pprime = add_points(multiply(L, pow(u, 2, p)), P, multiply(R, pow(u, -2, p)))
    Gprime = fold_points(G, pow(u, -1, p))
    Hprime = fold_points(H, u)

    aprime = fold_scalor(a, u)
    bprime = fold_scalor(b, pow(u, -1, p))

    return commitment_proof_log(Pprime, Gprime, Hprime, Q, aprime, bprime)



def vector_commit(points, scalars):
    return reduce(add, [multiply(P, i) for P, i in zip(points, scalars)], Z1)



a = [4,2,42,420]
b = [2,3,5,8]


G_vec = [(FQ(6286155310766333871795042970372566906087502116590250812133967451320632869759), FQ(2167390362195738854837661032213065766665495464946848931705307210578191331138)),
     (FQ(6981010364086016896956769942642952706715308592529989685498391604818592148727), FQ(8391728260743032188974275148610213338920590040698592463908691408719331517047)),
     (FQ(15884001095869889564203381122824453959747209506336645297496580404216889561240), FQ(14397810633193722880623034635043699457129665948506123809325193598213289127838)),
     (FQ(6756792584920245352684519836070422133746350830019496743562729072905353421352), FQ(3439606165356845334365677247963536173939840949797525638557303009070611741415))]

H_vec = [(FQ(13728162449721098615672844430261112538072166300311022796820929618959450231493), FQ(12153831869428634344429877091952509453770659237731690203490954547715195222919)),
    (FQ(17471368056527239558513938898018115153923978020864896155502359766132274520000), FQ(4119036649831316606545646423655922855925839689145200049841234351186746829602)),
    (FQ(8730867317615040501447514540731627986093652356953339319572790273814347116534), FQ(14893717982647482203420298569283769907955720318948910457352917488298566832491)),
    (FQ(419294495583131907906527833396935901898733653748716080944177732964425683442), FQ(14467906227467164575975695599962977164932514254303603096093942297417329342836))]

Q = (FQ(11573005146564785208103371178835230411907837176583832948426162169859927052980), FQ(895714868375763218941449355207566659176623507506487912740163487331762446439))

P = add_points(vector_commit(G_vec, a), vector_commit(H_vec, b), multiply(Q, np.inner(a, b)))


(P, G, H, Q, a, b) = commitment_proof_log(P, G_vec, H_vec, Q, a, b)

print (P == add_points(multiply(G[0], a[0]), multiply(H[0], b[0]), multiply(Q, a[0] * b[0])))