import numpy as np
import pickle
import pandas as pd
import math

def c_array(sbox):
    N = math.sqrt(len(sbox))
    if not N.is_integer():
        print("Invalid dimensions! Not a square sbox")
    
    formatted_elements = ["0x{:02X}".format(i).lower() for i in sbox]
    hex_vals = ["{:01X}".format(i) for i in range(int(N))]
    string = f"static const uint8_t sbox[{len(sbox)}] = {{\n"
    string += "// " + "     ".join("%s" %x for x in hex_vals) + "\n"
    for i, hex_str in enumerate(formatted_elements):
        if i % N == 0 and i != 0:
            string += f" // {hex_vals[int(i/N)-1]}\n"

        if i == len(formatted_elements)-1:
            string += hex_str
        else:
            string += hex_str + ", "
    string += f"   // {hex_vals[int(i/N)]}\n}};"
    return string

def generate_c_files():
    with open("aes_prelude.c.part", "r") as f:
        prelude = "".join(f.readlines())
    with open("aes_postlude.c.part", "r") as f:
        postlude = "".join(f.readlines())

    with open("sboxes_info.pkl", "rb") as f:
        sbox_df = pickle.load(f)

    sbox_dict = sbox_df.T.to_dict()

    for name in sbox_dict.keys():
        box = sbox_dict[name]["box"]
        aes_file = prelude + "\n" +  c_array(box) + "\n" + postlude
        with open(f"./c_files/{name}.c", "w") as f:
            f.write(aes_file)
    return 

generate_c_files()


