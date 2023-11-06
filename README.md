# S_Box_Complement
Creating/Testing Substitution Boxes (S-Boxes) and seeing if there is a "complementary S-box"

A Complementary S_box is defined as:

A 256-sized array such that the Hamming Weight of its elements added to another element is constant, and the two elements have a constant Hamming Distance.

That is, let 
* *w* be a constant for the Hamming Weight
* *d* be a constant for the Hamming Distance
* *S[i]* be the S-Box at position *i*
* *C[i]* be the Complementary S-Box at position *i*
  
Then

  Hamming_Weight(*S[i]* + *C[i]*) = *w* AND Hamming_Distance(*S[i]*, *C[i]*) = *d*

# How to Run
To run this project, simply run:
```
pip install -r requirements.txt
python3 main.py
```

# Verification in Lean
This project has some verification using Lean4. 
Here's how to set it up using the community project, Lean4.

## Setting up Lean
Make sure Lean is set up for your Operating System. 

- run `lake update` in the terminal
  - There might be some warnings about package configuration errors, caused by an incorrect toolchain version. This will be fixed in the next step.
  
- In the terminal, run `cp lake-packages/mathlib/lean-toolchain .` to make sure current Lean version matches mathlib4's.

- Run `lake update` again, there should not be any errors now.

- (Optionally) run `lake exe cache get` in the terminal to save time compiling mathlib and its dependencies

- Run `lake build` in the terminal

- Restart your instance of your IDE (VSCode, Emacs...)