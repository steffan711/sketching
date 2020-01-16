def generate_init_update(arr):
    updates = []
    for idx, val in enumerate(arr):
        updates.append("{} : (n'={})")

def generate_uniform(path, size):
    return generate_init_update([1/float(size) for i in range(size)])


generate_uniform(10)