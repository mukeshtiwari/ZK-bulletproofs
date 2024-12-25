from py_ecc.bn128 import G1, multiply, add, FQ, eq
from py_ecc.bn128 import curve_order as p
import random

def random_element():
    return random.randint(0, p)

# these EC points have unknown discrete logs:
G = (FQ(6286155310766333871795042970372566906087502116590250812133967451320632869759), FQ(2167390362195738854837661032213065766665495464946848931705307210578191331138))

H = (FQ(13728162449721098615672844430261112538072166300311022796820929618959450231493), FQ(12153831869428634344429877091952509453770659237731690203490954547715195222919))

B = (FQ(12848606535045587128788889317230751518392478691112375569775390095112330602489), FQ(18818936887558347291494629972517132071247847502517774285883500818572856935411))

# utility function
def addd(A, B, C):
    return add(A, add(B, C))

# scalar multiplication example: multiply(G, 42)
# EC addition example: add(multiply(G, 42), multiply(G, 100))

# remember to do all arithmetic modulo p
def commit(a_0, a_1, b_0, b_1, alpha, beta, tau_0, tau_1, tau_2):
    A = addd(multiply(G, a_0 % p), multiply(H, b_0 % p), multiply(B, alpha % p)) # A = a_0 * G + b_0 * H + alpha * B
    S = addd(multiply(G, a_1 % p), multiply(H, b_1 % p), multiply(B, beta % p)) # S = a_1 * G + b_1 * H + beta * B
    V = add(multiply(G, (a_0 * b_0) % p), multiply(B, tau_0 % p)) # V = a_0 * b_0 * G + tau_0 * B
    T1 = add (multiply(G, (a_0 * b_1 + a_1 * b_0) % p), multiply(B, tau_1 % p))  # T1 = a_0 * b_1 * G + a_1 * b_0 * G + tau_1 * B
    T2 = add (multiply(G, (a_1 * b_1) % p), multiply(B, tau_2 % p)) # T2 = a_1 * b_1 * G + tau_2 * B
    return (A, S, V, T1, T2)


def evaluate(f_0, f_1, f_2, u):
    return (f_0 + f_1 * u + f_2 * u**2) % p

def prove(blinding_0, blinding_1, blinding_2, u):
    return (blinding_0 + blinding_1 * u + blinding_2 * u**2) % p

## step 0: Prover and verifier agree on G and B

## step 1: Prover creates the commitments
a_0 = random_element()
b_0 = random_element()
a_1 = random_element()
b_1 = random_element()
t1 = (a_0 * b_1 + a_1 * b_0) % p
t2 = (a_1 * b_1) % p

### blinding terms
alpha = random_element()
beta = random_element()
tau_0 = random_element()
tau_1 = random_element()
tau_2 = random_element()

A, S, V, T1, T2 = commit(a_0, a_1, b_0, b_1, alpha, beta, tau_0, tau_1, tau_2)

## step 2: Verifier picks u
u = random_element()

## step 3: Prover evaluates l(u), r(u), t(u) and creates evaluation proofs
l_u = evaluate(a_0, a_1, 0, u)
r_u = evaluate(b_0, b_1, 0, u)
t_u = evaluate(a_0*b_0, t1, t2, u)

pi_lr = prove(alpha, beta, 0, u)
pi_t = prove(tau_0, tau_1, tau_2, u)

## step 4: Verifier accepts or rejects
assert t_u  == (l_u * r_u) % p, "tu != lu*ru"
assert eq(add(A, multiply(S, u)), addd(multiply(G, l_u), multiply(H, r_u), multiply(B, pi_lr))), "l_u or r_u not evaluated correctly"
assert eq(add(multiply(G, t_u), multiply(B, pi_t)), addd(V, multiply(T1, u), multiply(T2, u**2 % p))), "t_u not evaluated correctly"
