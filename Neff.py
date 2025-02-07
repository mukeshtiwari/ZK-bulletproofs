from Crypto.Util.number import getPrime, getRandomRange, isPrime
from typing import List, Tuple 
from functools import reduce


# Helper functions
def mod_exp(base, exp, mod):
  return pow(base, exp, mod)


def generate_safe_prime(bits):
  while True:
    q = getPrime(bits - 1)
    p = 2 * q + 1
    if isPrime(p):
      return p, q

# print(generate_safe_prime(64))

class ILMPP: 
  def __init__(self, bits):
    self.p, self.q =  generate_safe_prime(bits)
    self.g = 4
    assert pow(self.g, self.q, self.p) == 1
    self.x = getRandomRange(1, self.q)
    self.h = mod_exp(self.g, self.x, self.p)

  # Prover knows: x_i = log_g X_i, y_i = log_g Y_i
  def prover(self, X : List[int], Y : List[int], x : List[int], y : List[int], gamma : int) -> Tuple[List[int], List[int]]:
    k = len(X)
    assert len(Y) == k
    assert len(x) == k
    assert len(y) == k
    
    #step 1: generate commitment A1, A2, ... Ak
    theta = [getRandomRange(1, self.q) for _ in range(k - 1)]
    A = [mod_exp(Y[0], theta[0], self.p)]
    for i in range(1, k - 1):
        A.append((mod_exp(X[i], theta[i - 1], self.p) * mod_exp(Y[i], theta[i], self.p)) % self.p)
    A.append(mod_exp(X[k - 1], theta[k - 2], self.p))

    #step 2: get a random challenge from verifier
    # In practice, we should use Fiat-Shamir heuristic to generate the challenge
    # gamma = getRandomRange(1, self.q)

    #step 3: generate response r1, r2, ... rk
    r = [] 
    sign = -gamma 
    acc = 1  
    for i in range(0, k - 1) :
      acc = (acc * (x[i] * mod_exp (y[i], -1, self.q))) % self.q
      r.append((theta[i] + sign * acc) % self.q)
      sign = -sign 
    
    return A, r
  

  def verifier(self, X : List[int], Y : List[int], A : List[int], r : List[int], gamma) -> bool: 
    k = len(X)
    assert len(Y) == k
    assert len(A) == k
    assert len(r) == (k - 1)

    ret = (pow(Y[0], r[0], self.p) == ((A[0] * pow(X[0], -gamma, self.p)) % self.p))
    for i in range(1, k - 1):
      ret = (ret and (pow(X[i], r[i - 1], self.p) * pow(Y[i], r[i], self.p) % self.p == A[i]))
    ret = (ret and pow(X[k - 1], r[k - 2], self.p) == (A[k - 1] * pow(Y[k - 1], ((-1) ** (k - 1)) * gamma, self.p)) % self.p)

    return ret

    

#Testing code     
ilmpp = ILMPP(100)
N = 100 
x = [getRandomRange(1, ilmpp.q) for _ in range(N)]
y = [e for e in x]

c, d, e, f, g, h = (getRandomRange(1, ilmpp.q) for _ in range(6))

x[0] *= c
x[7] *= d
x[2] *= e
x[0] *= f
x[0] *= g
x[3] *= h
y[1] *= c
y[9] *= d
y[2] *= e
y[5] *= f
y[8] *= g
y[8] *= h

X = [pow(ilmpp.g, x[i], ilmpp.p) for i in range(N)]
Y = [pow(ilmpp.g, y[i], ilmpp.p) for i in range(N)]
gamma = getRandomRange(1, ilmpp.q)
A, r = ilmpp.prover(X, Y, x, y, gamma)

#print(x, y, X, Y, A, r)
print(ilmpp.verifier(X, Y, A, r, gamma))

