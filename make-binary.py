import sys

if __name__ == '__main__':
    if len(sys.argv) != 1:
        print('usage: {}'.format(sys.argv[0]))
        sys.exit(1)
    inp = 'output.wasm.txt' # sys.argv[1]
    out = 'output.wasm' # sys.argv[2]
    with open(inp) as f:
        inp = f.read()
    b = [int(x, 16) for x in inp.split()]
    with open(out, 'wb') as f:
        f.write(bytearray(b))
    print('written {}'.format(out))
