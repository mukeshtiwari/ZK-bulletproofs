from py_ecc.bn128 import G1, multiply, add, FQ
from py_ecc.bn128 import curve_order as p
import random

def random_field_element():
    return random.randint(0, p)

# these EC points have unknown discrete logs:
G = (FQ(6286155310766333871795042970372566906087502116590250812133967451320632869759), FQ(2167390362195738854837661032213065766665495464946848931705307210578191331138))

B = (FQ(12848606535045587128788889317230751518392478691112375569775390095112330602489), FQ(18818936887558347291494629972517132071247847502517774285883500818572856935411))

# scalar multiplication example: multiply(G, 42)
# EC addition example: add(multiply(G, 42), multiply(G, 100))

# remember to do all arithmetic modulo p
# This is important: all arithmetic is done modulo p. If you 
# reduce the scalors mod filed_mod, you are forgetting 
# the group structure of the elliptic curve.


def commit(c_0, c_1, c_2, gamma_0, gamma_1, gamma_2, G, B):
    # fill this in
    C0 = add (multiply(G, c_0 % p), multiply(B, gamma_0 % p)) # C0 = c_0 * G + gamma_0 * B
    C1 = add (multiply(G, c_1 % p), multiply(B, gamma_1 % p)) # C1 = c_1 * G + gamma_1 * B
    C2 = add (multiply(G, c_2 % p), multiply(B, gamma_2 % p)) # C2 = c_2 * G + gamma_2 * B
    return (C0, C1, C2)

def evaluate(c_0, c_1, c_2, u):
    return (c_0 + c_1 * u + c_2 * u**2) % p

def prove(gamma_0, gamma_1, gamma_2, u):
    return (gamma_0 + gamma_1 * u + gamma_2 * u**2) % p
    

def verify(C0, C1, C2, G, B, f_u, pi):
    lhs = add(multiply(G, f_u % p), multiply(B, pi % p))
    rhs = add(C0, add(multiply(C1, u % p), multiply(C2, u**2 % p)))
    return lhs == rhs # f_u * G + pi * B == C0 + C1 * u + C2 * u^2

## step 0: Prover and verifier agree on G and B

## step 1: Prover creates the commitments
### f(x) = c_0 + c_1x + c_2x^2
c_0 = random_field_element()
c_1 = random_field_element()
c_2 = random_field_element()

### blinding terms
gamma_0 = random_field_element()
gamma_1 = random_field_element()
gamma_2 = random_field_element()
C0, C1, C2 = commit(c_0, c_1, c_2, gamma_0, gamma_1, gamma_2, G, B)

## step 2: Verifier picks u
u = random_field_element()

## step 3: Prover evaluates f(u) and pi

f_u = evaluate(c_0, c_1, c_2, u)
pi = prove(gamma_0, gamma_1, gamma_2, u)

## step 4: Verifier accepts or rejects
if verify(C0, C1, C2, G, B, f_u, pi):
    print("accept")
else:
    print("reject")
