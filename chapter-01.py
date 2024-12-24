from py_ecc.bn128 import is_on_curve, FQ
from py_ecc.fields import field_properties
field_mod = field_properties["bn128"]["field_modulus"]
from hashlib import sha256
from libnum import has_sqrtmod_prime_power, sqrtmod_prime_power

b = 3 # for bn128, y^2 = x^3 + 3
seed = "RareSkills"
x = int(sha256(seed.encode('ascii')).hexdigest(), 16) % field_mod
vector_basis = []

# modify the code below to generate n points
# on the curve y^2 = x^3 + b
n = 10

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


print(vector_basis)
