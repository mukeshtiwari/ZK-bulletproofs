from py_ecc.bn128 import multiply, add, neg, FQ, eq, Z1
from py_ecc.bn128 import curve_order as p
import numpy as np
from functools import reduce
import random


def add_points(*points):
  return reduce(add, points, Z1)

def inner_product(a, b):
  return sum((ai * bi) % p for ai, bi in zip(a, b)) % p

def vector_commit(points, scalars):
  return reduce(add, [multiply(P, i) for P, i in zip(points, scalars)], Z1)


def commit(a, sL, b, sR, alpha, beta, tau_0, tau_1, tau_2, G, H, Q, B):
  # A = <a, G> + <b, H> + alpha * B 
  A = add_points(vector_commit(G, a), vector_commit(H, b), multiply(B, alpha % p)) 
  # S = <sL, G> + <sR, H> + beta * B
  S = add_points(vector_commit(G, sL), vector_commit(H, sR), multiply(B, beta % p)) 
  v = inner_product(a, b) % p
  # V = v * Q + tau_0 * B
  V = add(multiply(Q, v), multiply(B, tau_0 % p))
  # T1 = (<a, sR> + <sL, b>) * G + tau_1 * B              
  T1 = add(multiply(Q, inner_product(a, sR) + inner_product(sL, b)), multiply(B, tau_1 % p))
  # T2 = <sL, sR> * G + tau_2 * B  
  T2 = add(multiply(Q, inner_product(sL, sR)), multiply(B, tau_2))        
  return (A, S, V, T1, T2)


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


# a + sL * u 
def evaluate(a, b, u):
  return [(x + u * y) % p for x, y in zip(a, b)]


# Testing code
from py_ecc.bn128 import is_on_curve
from py_ecc.fields import field_properties
field_mod = field_properties["bn128"]["field_modulus"]
from hashlib import sha256
from libnum import has_sqrtmod_prime_power, sqrtmod_prime_power
import random

def random_element():
  return random.randint(0, p)

def random_scalar_vector(n):
  return [random_element() for _ in range(n)]


def generate_n_EC_point(n : int, seed : str):
  b = 3 # for bn128, y^2 = x^3 + 3
  x = int(sha256(seed.encode('ascii')).hexdigest(), 16) % field_mod
  vector_basis = []

  while len(vector_basis) < n:
    entropy = 0  
    while True : 
      x = (x + entropy) % field_mod
      y_squared = (x**3 + b) % field_mod
      if has_sqrtmod_prime_power(y_squared, field_mod, 1):
        y = list(sqrtmod_prime_power(y_squared, field_mod, 1))[entropy % 2]
        vector_basis.append((FQ(x), FQ(y)))
        assert is_on_curve(vector_basis[-1], b)
        break
      entropy += 1
        
    x = int(sha256(str(x).encode('ascii')).hexdigest(), 16) % field_mod

  return vector_basis


def generate_data():
  n = 16 # should be a power of 2
  G = generate_n_EC_point(n, "RareSkillsFirstseed")
  H = generate_n_EC_point(n, "RareSkillsSecondseed")
  Q = generate_n_EC_point(1, "RareSkillsThirdseed")[0]
  B = generate_n_EC_point(1, "RareSkillsFourthseed")[0]

  a = random_scalar_vector(n)
  b = random_scalar_vector(n)
  sL = random_scalar_vector(n)
  sR = random_scalar_vector(n)
  alpha = random_element()
  beta = random_element()
  tau_0 = random_element()
  tau_1 = random_element()
  tau_2 = random_element()

  A, S, V, T1, T2 = commit(a, sL, b, sR, alpha, beta, tau_0, tau_1, tau_2, G, H, Q, B)

  # verifier picks a random u (Ideally, Fiat-Shamir heuristic should be used)
  u = random_element()

  # Compute l(u), r(u), t(u) and creates evaluation proofs
  l_u = evaluate(a, sL, u) # l(u) = a + sL * u
  r_u = evaluate(b, sR, u) # r(u) = b + sR * u
  t_u = (inner_product(a, b) + (((inner_product(a, sR) + inner_product(b, sL)) % p) * u) % p + (inner_product(sL, sR) * pow(u, 2, p)) % p) % p

  pi_lr = alpha + (beta * u % p) % p # pi_lr = alpha + beta * u
  pi_t = tau_0 + (tau_1 * u % p) + (tau_2 * pow(u, 2, p) % p) # pi_t = tau_0 + tau_1 * u + tau_2 * u^2

  P = add_points(vector_commit(G, l_u), vector_commit(H, r_u)) # C = <l(u), G> + <r(u), H>

  (Pprime, Gprime, Hprime, Qprime, aprime, bprime) = commitment_proof_log(add_points(P, multiply(Q, t_u)), G, H, Q, l_u, r_u)
  # P' = a' * G' + b' * H' + Q' * t(u)
  ret = (Pprime == add_points(multiply(Gprime[0], aprime[0]), multiply(Hprime[0], bprime[0]), multiply(Qprime, aprime[0] * bprime[0])))
  # P = A + S * u - B * pi_lr
  ret = ret and (P == add_points(A, multiply(S, u), neg(multiply(B, pi_lr))))
  # t_u * Q = V + T1 * u + T2 * u^2 - B * pi
  ret = ret and multiply(Q, t_u) == add_points(V, multiply(T1, u), multiply(T2, pow(u, 2, p)), neg(multiply(B, pi_t)))
  return ret 
    

def __main__() : 
  ret = generate_data()
  print(ret)

__main__()

# Test cases
#a1 = [808, 140, 166, 209]
#b1 = [88, 242, 404, 602]

#a2 = [433, 651]
#b2 = [282, 521]

#a3 = [222]
#a4 = [313]

# Prove you know the inner product of a and b using a combination of the algorithm from Chapter 5 and Chapter 7.
# Your interactive proof should transmit no more than logarithmic size data and be zero knowledge even if n = 1.
# Use a random elliptic curve basis based on the algorithm from Chapter 1.
