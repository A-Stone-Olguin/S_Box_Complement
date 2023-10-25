import pandas as pd

def Hamming_Weight_Table():
    HW = [bin(n).count("1") for n in range(0, 256)]
    counts = [0]*9
    for i in HW:
        counts[i] +=1
    hw_data = {"Count":counts}
    hw_df = pd.DataFrame.from_dict(hw_data)
    hw_df.index.name = "HW"
    return hw_df

def main():
    hws_table = Hamming_Weight_Table()
    print(hws_table)
    return

if __name__ == "__main__":
    main()