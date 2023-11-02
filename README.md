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