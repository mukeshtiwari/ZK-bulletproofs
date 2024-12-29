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


def verify_commitment_proof_log(P, G, a):
  n = len(a)
  if n == 1:
    return eq(P, multiply(G[0], a[0]))
  else:
    L, R = compute_secondary_diagonal(G, a)
    # random scalar from verifier
    u = random_element()
    #fold group elements and scalars
    Gprime = fold_points(G, pow(u, -1, p))
    Pprime = add_points(multiply(L, pow(u, 2, p)), P, multiply(R, pow(u, -2, p)))
    aprime = fold_scalor(a, u)

    return verify_commitment_proof_log(Pprime, Gprime, aprime)


    
def vector_commit(points, scalars):
    return reduce(add, [multiply(P, i) for P, i in zip(points, scalars)], Z1)

G_vec = [(FQ(6286155310766333871795042970372566906087502116590250812133967451320632869759), FQ(2167390362195738854837661032213065766665495464946848931705307210578191331138)),
     (FQ(6981010364086016896956769942642952706715308592529989685498391604818592148727), FQ(8391728260743032188974275148610213338920590040698592463908691408719331517047)),
     (FQ(15884001095869889564203381122824453959747209506336645297496580404216889561240), FQ(14397810633193722880623034635043699457129665948506123809325193598213289127838)),
     (FQ(6756792584920245352684519836070422133746350830019496743562729072905353421352), FQ(3439606165356845334365677247963536173939840949797525638557303009070611741415))]

a = [4,2,42,420]
P = vector_commit(G_vec, a)

print(P)

Pt = verify_commitment_proof_log(P, G_vec, a)

print(Pt)