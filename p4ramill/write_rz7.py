import sys
content = sys.stdin.read()
with open('Imscribing/RZ7GroupAlgebra.lean', 'w') as f:
    f.write(content)
print('written', len(content))
