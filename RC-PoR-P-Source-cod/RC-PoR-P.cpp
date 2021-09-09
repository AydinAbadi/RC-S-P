// This is a source code of "recurring contingent proofs of retreivability payment (RC-PoR-P)" in C++. 
// It includes Merkle tree functions (a) build_MT_tree, (b) gen_proof, and (c) verify_proof that is of independent interest. 
// Moreover, regarding the Merkle tree, two additional functions: (a) gen_encrypted_proof and (b) verify_encrypted_proof have been provided. 
// These two functions can be used when there is a need to efficiently generate encrtped proofs and verify the encrypted proofs. 
// To encrypt such proofs efficiently one-time pad has been used in this implementation. 


/////////////////////////////////
// # Dependencies: 
//   Cryptopp: https://cryptopp.com
//   The GNU Multiple Precision Arithmetic Library (GMP): https://gmplib.org
////////////////////////////////
//# Runnig a Test:
//   (1) clone the above libraries, as well as the ``RC-PoR-P-Source-code`` repository. 
//   (2) install the libraries and unzip the ``RC-PoR-P-Source-code-main`` file. 
//   (3) run the following command lines in order:
//        cd RC-PoR-P-Source-code-main
//        g++ -c Rand.cpp
//        g++ -I /PATH-TO-CRYPTOPP Rand.o RC-PoR-P.cpp /Users/PATH-TO:libcryptopp.a  -o main -lgmpxx -lgmp
//       ./main
//////////////////////////////


#include <iostream>
#include <math.h>
#include <string>
#include <stdio.h>
#include <vector>
#include "gmp.h"
#include <gmpxx.h>
#include "Rand.h"
#include "cryptopp/cryptlib.h"
#include "cryptopp/sha.h"
#include "cryptopp/filters.h"
#include "cryptopp/hex.h"
#include "cryptopp/secblock.h"
#include "cryptopp/osrng.h"
#include "cryptopp/cryptlib.h"
using CryptoPP::AutoSeededRandomPool;
using CryptoPP::CTR_Mode;
using namespace CryptoPP;
using namespace std;
typedef mpz_t bigint;
typedef unsigned char byte;

//===============================
// description: converts integer "n" to a binary string.
string toBinary(int n){

  string res;
  while(n != 0) {
    res = (n % 2 == 0 ?"0":"1") + res;
    n /= 2;
  }
  return res;
}

//===============================
// description: concatenates file block ''b_j''  with its index j (i.e., computes b_j || j)
bigint* encode_file(bigint* file, int file_size, int pad_size){

  bigint* encoded_file;
  string str_file, str_index, str_diff, str_padded_file;
  int diff;
  encoded_file = (bigint*)malloc(file_size * sizeof(bigint));
  for(int i = 0; i < file_size; i++){
    // convert each file block into bitstring
    str_file = mpz_get_str (NULL, 2, file[i]);
    // convert integer i to binary string.
    str_index = toBinary(i);
    // pad the file with fixed size tail
    if(str_index.length() < pad_size){
      diff = pad_size - str_index.length();
      for(int i = 0; i < diff; i++){
        str_diff += '0';
      }
    }
    str_padded_file = str_file + str_diff + str_index;
    // convert bitstring to bigint.
    char* ar = new char[str_padded_file.length() + 1];
    strcpy(ar, str_padded_file.c_str());
    mpz_init_set_str(encoded_file[i], ar, 2);
    str_padded_file.clear();
    str_index.clear();
    str_file.clear();
    str_diff.clear();
  }
  return encoded_file;
}

//===============================
// description: checks if element ''val'' exists in ''array''.
bool search(int* array, int size, int val){

  for (int i = 0; i < size; ++i){
    if (array[i] == val){
      return true;
    }
  }
  return false;
}

//===============================
// description: removes from  encoded block ''b_j||j'' its tail "j".
int extract_tail(bigint encoded_file, int pad_size){

  int extracted_tail;
  string str_file, sub_str_file;
  str_file = mpz_get_str (NULL, 2, encoded_file);// convert the bigint to bitstring
  sub_str_file = str_file.substr(str_file.length() - pad_size, pad_size);// extract the tail
  // convert the tail (in bitstring) to an integer.
  char* char_;
  char_ = new char[sub_str_file.length() + 1];
  strcpy(char_, sub_str_file.c_str());
  char * pEnd;
  extracted_tail = strtoull (char_, &pEnd, 2);
  str_file.clear();
  sub_str_file.clear();
  return extracted_tail;
}

//===============================
// description: given values ''a'' and ''b'', it returns hash(a||b)
bigint* hash_combined_values(bigint val_1, bigint val_2, bigint modulus){
  string s_val_1, s_val_2, s_val_com;
  CryptoPP::SHA256 hash2;
  byte digest[CryptoPP::SHA256::DIGESTSIZE];
  bigint* res;
  res = (bigint*)malloc(1 * sizeof(bigint));
  s_val_1 = mpz_get_str(NULL, 10, val_1);
  s_val_2 = mpz_get_str(NULL, 10, val_2);
  s_val_com = s_val_1 + s_val_2;
  unsigned int nDataLen = s_val_com.length();
  hash2.CalculateDigest(digest, (byte*)s_val_com.c_str(), nDataLen);
  s_val_com.clear();
  s_val_1.clear();
  s_val_2.clear();
  mpz_init(res[0]);
  mpz_import(res[0], sizeof(digest), 1, sizeof(digest[0]), 0, 0, digest);
  mpz_mod(res[0], res[0], modulus);
  return res;
}

//===============================
// description: build a Merkle tree on top of array of blocks: "file"
bigint** build_MT_tree(bigint* file, int file_size, bigint modulus){

  CryptoPP::SHA256 hash2;
  byte digest[CryptoPP::SHA256::DIGESTSIZE];
  int number_of_levels = log2(file_size);// number of levels excluding leaf nodes level
  bigint** nodes;
  bigint* res_;
  nodes = (bigint**)malloc(number_of_levels * sizeof(bigint));// initiate a 2-D array
  int temp_size_1, j, temp_size_2;
  for (int  k = 0; k < number_of_levels; k++){
    temp_size_1 = file_size/(pow(2, k+1));//number of nodes in each level starting from one level up the leaf nodes
    nodes[k] = (mpz_t*)malloc(temp_size_1 * sizeof(mpz_t));// initiate each array
    j = 0;
    temp_size_2 = file_size/(pow(2, k));
    for(int i = 0; i < temp_size_2;){
      if(k == 0){
        res_ = hash_combined_values(file[i], file[i+1], modulus);
        mpz_init_set(nodes[k][j], res_[0]);
        mpz_clear(res_[0]);
        j++;
        i += 2;
      }
      else{
        res_ = hash_combined_values(nodes[k-1][i], nodes[k-1][i+1], modulus);
        mpz_init_set(nodes[k][j], res_[0]);
        mpz_clear(res_[0]);
        j++;
        i += 2;
      }
    }
  }
  return nodes;
}

//===============================
// description: checks array ''ar'' contains duplicated element.
bool is_there_duplicated_elem(int* ar, int ar_size){

  int counter;
  int temp;
  for(int i = 0; i < ar_size; i++){
    temp = ar[i];
    counter = 0;
    for(int j = 0; j < ar_size; j++){
      if(ar[j] == temp){
        counter++;
      }
    }
    if (counter > 1){
      return true;
    }
  }
  return false;
}

//===============================
// description: generates an array of random challenges: "chall". Currently it does not check if the array contains
// repeated elements. If the duplication needs ot be check then the below while loop can be commented in.
int* gen_chall_(int number_of_chall, int bit_size_of_chall, int int_modulus){

    Random rd_;
    int* ar;
    ar = new int[number_of_chall];
    bigint* set, bigint_modulus;
    bool duplicated_ = true;
    set = (bigint*)malloc(number_of_chall * sizeof(bigint));
    // while(duplicated_){// this loop can be commented out/in if duplication is (not) allowed.
    set = rd_.gen_randSet(number_of_chall, bit_size_of_chall);// generate a set of random bigint
    // put them in the range: [0,int_modulus-1]
    mpz_init(bigint_modulus);
    mpz_set_ui(bigint_modulus, int_modulus);
    for (int i = 0; i < number_of_chall; i++){
      mpz_mod(set[i], set[i], bigint_modulus);
      ar[i] = mpz_get_ui(set[i]);
      mpz_clear(set[i]);
    }
     //duplicated_ = is_there_duplicated_elem(ar, number_of_chall);
    //}
    // if(duplicated_){
    //   cout<<"\n\n\t\t*******************************************************"<<endl;
    //   cout<<"\n\n\t\tNOTE: The challange array contains duplicated values--Pick a new array"<<endl;
    //   cout<<"\n\n\t\t*******************************************************"<<endl;
    // }
    return ar;
}

//===============================
// description: finds an index of a value: valu, in "set".
// This fubnction is called by the proof generation fubnction to locate a node's index given its value.
int find_index(bigint* set, int set_size, bigint val, bool &res_, int offset){

  int res;
  for(int i = offset-1; i < set_size; i++){
    if (mpz_cmp(set[i], val) == 0){
      res_ = true;
      return i;// 0 means val exists in the set
    }
  }
  res_ = false;
  return 0;
}

//===============================
// description: generates Merkle tree proof (a set of paths)
// this function is used when the proof's elements do not need to be encrypted.
bigint*** gen_proof(int number_of_chall, int* challenge, bigint* file, int file_size, bigint** nodes, bigint modulus){

  bigint*** proof;
  proof = (bigint***)malloc(number_of_chall * sizeof(bigint));
  int size_1 = log2(file_size) + 2; //number of elements in each proof (related to each challenge)
  int number_of_levels = log2(file_size) + 1;// number of levels in the tree including leaf nodes
  bigint* temp_hash;
  temp_hash = (mpz_t*)malloc(1 * sizeof(mpz_t));
  int offset;
  for(int i = 0; i < number_of_chall; i++){
    offset = 0;
    proof[i] = (bigint**)malloc(size_1 * sizeof(bigint));
    // go through different levels of the tree including leaf nodes
    int j = 0;
    for (int  k = 0; k < number_of_levels; k++){
      if(k == 0){
        offset = sqrt(challenge[i]);
        if(challenge[i] % 2 == 0){ // if challenge[i] (or the index of challenged file block) is even
          proof[i][j] = (bigint*)malloc(2 * sizeof(bigint));
          mpz_init_set(proof[i][j][0], file[challenge[i]]); // insert leaf node file[challenge[i]] to the proof
          mpz_init_set_str(proof[i][j][1], "0", 10);
          j++;
          proof[i][j] = (bigint*)malloc(2 * sizeof(bigint));
          mpz_init_set(proof[i][j][0], file[challenge[i] + 1]); // insert the next leaf node file: [challenge[i]] to the proof
          mpz_init_set_str(proof[i][j][1], "0", 10);
          j++;
         // generate hash(file[challenge[i]] ||file[challenge[i]+1])
          temp_hash = hash_combined_values(file[challenge[i]],file[challenge[i] + 1], modulus);
        }
        else{ // if challenge[i] is odd
          proof[i][j] = (bigint*)malloc(2 * sizeof(bigint));
          mpz_init_set(proof[i][j][0], file[challenge[i]-1]); // insert leaf node file[challenge[i]] to the proof
          mpz_init_set_str(proof[i][j][1], "0", 10);
          j++;
          proof[i][j] = (bigint*)malloc(2 * sizeof(bigint));
          mpz_init_set(proof[i][j][0], file[challenge[i]]); // insert the next leaf node file: [challenge[i]] to the proof
          mpz_init_set_str(proof[i][j][1], "0", 10);
          j++;
          temp_hash = hash_combined_values(file[challenge[i]-1], file[challenge[i]], modulus);
        }
      }
      else{ // if k is not zero--   // find the index of temp_hash in the next level node
        int nonil = file_size/(pow(2, k));//nonil: number_of_nodes_inEach_level
        bool res_;
        int index = find_index(nodes[k-1], nonil, temp_hash[0], res_, offset); // find the index of temp_hash in nodes[k-1]
        offset = sqrt(index);
        if(index % 2 == 0 && res_){
          if(index == 0 && k+1 == number_of_levels){
            proof[i][j] = (bigint*)malloc(2 * sizeof(bigint));
            mpz_init_set(proof[i][j][0], nodes[k-1][index]);
            mpz_init_set_str(proof[i][j][1], "0", 10);
          }
          else{
            proof[i][j] = (bigint*)malloc(2 * sizeof(bigint));
            mpz_init_set(proof[i][j][0], nodes[k-1][index+1]);
            mpz_init_set_str(proof[i][j][1], "0", 10);
            j++;
            temp_hash = hash_combined_values(nodes[k-1][index], nodes[k-1][index+1], modulus);
          }
        }
        else if(index % 2 != 0 && res_){
          proof[i][j] = (bigint*)malloc(2 * sizeof(bigint));
          mpz_init_set(proof[i][j][0], nodes[k-1][index-1]);
          mpz_init_set_str(proof[i][j][1], "1", 10);
          j++;
          temp_hash = hash_combined_values(nodes[k-1][index-1], nodes[k-1][index], modulus);
        }
      }
    }
  }
  mpz_clear(temp_hash[0]);
  return proof;
}

//=================================
// description: encrypts "val" given the key and initial vector.
bigint* encrypt(int val, byte* key, int key_size, byte* iv, int byte_){

  string cipher, temp;
  CBC_Mode< AES >::Encryption e;
  bigint* res;
  res = (bigint*)malloc(1 * sizeof(mpz_t));
  unsigned char prn_[byte_];
  e.SetKeyWithIV(key, key_size, iv);
  StringSource sss(to_string(val), true, new StreamTransformationFilter(e, new StringSink(cipher)));
  temp = cipher.substr (0, byte_);// truncate the ciphertext
  memset(prn_, 0x00, byte_ + 1);
  strcpy((char*)prn_, temp.c_str());
  mpz_init(res[0]);
  mpz_import(res[0], byte_, 1, 1, 0, 0, prn_);
  return res;
}

//===============================
// description: generates Merkle tree proof (a set of paths)
// this function is used when the proof's elements do need to be encrypted.
bigint*** gen_encrypted_proof(int number_of_chall, int* challenge, bigint* file, int file_size, bigint** nodes, byte* key, byte* iv, int key_size, bigint* modulus, int byte_){

  bigint*** proof;
  proof = (bigint***)malloc(number_of_chall * sizeof(bigint));
  int size_1 = log2(file_size) + 2; // number of elements in each proof (related to each challenge)
  int number_of_levels = log2(file_size) + 1;// number of levels in the tree including leaf nodes
  bigint* temp_hash, *temp_val;
  string temp;
  int offset;
  unsigned char prn_[byte_];
  temp_hash = (mpz_t*)malloc(1 * sizeof(mpz_t));
  temp_val = (mpz_t*)malloc(1 * sizeof(mpz_t));
  string cipher;
  CBC_Mode< AES >::Encryption e;
	e.SetKeyWithIV(key, key_size, iv);// set the key
  unsigned char der_key_0[key_size]; // convert the ciphertext into a der_key
  int j;
  double time_encrypt;//only  for test
  for(int i = 0; i < number_of_chall; i++){
    offset = 0;
    // derive a key for each index i
    StringSource s(to_string(i), true, new StreamTransformationFilter(e, new StringSink(cipher)));// encrypt the str_index
	  memset(der_key_0, 0x00, key_size + 1);
	  strcpy((char*)der_key_0, cipher.c_str());
	  cipher.clear();
    proof[i] = (bigint**)malloc(size_1 * sizeof(bigint));
    // go through different levels of the tree including leaf nodes
    j = 0;
    for (int  k = 0; k < number_of_levels; k++){
      if(k == 0){
        offset = sqrt(challenge[i]);
        if(challenge[i] % 2 == 0){ // if challenge[i] (or the index of challenged file block) is even
          proof[i][j] = (bigint*)malloc(2 * sizeof(bigint));
          mpz_init_set(proof[i][j][0], file[challenge[i]]); // insert leaf node file[challenge[i]] to the proof
          // blinds each proof
          temp_val = encrypt(j, der_key_0, key_size, iv, byte_);
          mpz_add(proof[i][j][0], proof[i][j][0], temp_val[0]); // blinds each proof
          mpz_mod(proof[i][j][0], proof[i][j][0], modulus[0]);
          mpz_init_set_str(proof[i][j][1], "0", 10);
          j++;
          proof[i][j] = (bigint*)malloc(2 * sizeof(bigint));
          mpz_init_set(proof[i][j][0], file[challenge[i] + 1]); // insert the next leaf node file: [challenge[i]] to the proof
          //// blinds each proof
          temp_val = encrypt(j, der_key_0, key_size, iv, byte_);
          mpz_add(proof[i][j][0], proof[i][j][0], temp_val[0]); // blinds each proof
          mpz_mod(proof[i][j][0], proof[i][j][0], modulus[0]);
          mpz_init_set_str(proof[i][j][1], "0", 10);
          j++;
          // generate hash(file[challenge[i]] ||file[challenge[i]+1])
          temp_hash = hash_combined_values(file[challenge[i]],file[challenge[i] + 1], modulus[0]);
        }
        else{ // if challenge[i] is odd
          proof[i][j] = (bigint*)malloc(2 * sizeof(bigint));
          mpz_init_set(proof[i][j][0], file[challenge[i]-1]); // insert leaf node file[challenge[i]] to the proof
          // blinds each proof
          temp_val = encrypt(j, der_key_0, key_size, iv, byte_);
          mpz_add(proof[i][j][0], proof[i][j][0], temp_val[0]); // blinds each proof
          mpz_mod(proof[i][j][0], proof[i][j][0], modulus[0]);
          mpz_init_set_str(proof[i][j][1], "0", 10);
          j++;
          proof[i][j] = (bigint*)malloc(2 * sizeof(bigint));
          mpz_init_set(proof[i][j][0], file[challenge[i]]); // insert the next leaf node file: [challenge[i]] to the proof
          // blinds each proof
          temp_val = encrypt(j, der_key_0, key_size, iv, byte_);
          mpz_add(proof[i][j][0], proof[i][j][0], temp_val[0]); // blinds each proof
          mpz_mod(proof[i][j][0], proof[i][j][0], modulus[0]);
          mpz_init_set_str(proof[i][j][1], "0", 10);
          j++;
          temp_hash = hash_combined_values(file[challenge[i]-1], file[challenge[i]], modulus[0]);
        }
      }
      else{ // if k is not zero--   // find the index of temp_hash in the next level node
        int nonil = file_size/(pow(2, k));// nonil: number_of_nodes_inEach_level
        bool res_;
        int index = find_index(nodes[k-1], nonil, temp_hash[0], res_, offset); // find the index of temp_hash in nodes[k-1]
        offset = sqrt(index);
        if(index % 2 == 0 && res_){
          if(index == 0 && k+1 == number_of_levels){
            proof[i][j] = (bigint*)malloc(2 * sizeof(bigint));
            mpz_init_set(proof[i][j][0], nodes[k-1][index]);
            // blinds each proof
            temp_val = encrypt(j, der_key_0, key_size, iv, byte_);
            mpz_add(proof[i][j][0], proof[i][j][0], temp_val[0]); // blinds each proof
            mpz_mod(proof[i][j][0], proof[i][j][0], modulus[0]);
            mpz_init_set_str(proof[i][j][1], "0", 10);
          }
          else{
            proof[i][j] = (bigint*)malloc(2 * sizeof(bigint));
            mpz_init_set(proof[i][j][0], nodes[k-1][index+1]);
            // blinds each proof
            temp_val = encrypt(j, der_key_0, key_size, iv, byte_);
            mpz_add(proof[i][j][0], proof[i][j][0], temp_val[0]); // blinds each proof
            mpz_mod(proof[i][j][0], proof[i][j][0], modulus[0]);
            mpz_init_set_str(proof[i][j][1], "0", 10);
            j++;
            temp_hash = hash_combined_values(nodes[k-1][index], nodes[k-1][index+1], modulus[0]);
          }
        }
        else if(index % 2 != 0 && res_){
          proof[i][j] = (bigint*)malloc(2 * sizeof(bigint));
          mpz_init_set(proof[i][j][0], nodes[k-1][index-1]);
          // blinds each proof
          temp_val = encrypt(j, der_key_0, key_size, iv, byte_);
          mpz_add(proof[i][j][0], proof[i][j][0], temp_val[0]); // blinds each proof
          mpz_mod(proof[i][j][0], proof[i][j][0], modulus[0]);
          mpz_init_set_str(proof[i][j][1], "1", 10);
          j++;
          temp_hash = hash_combined_values(nodes[k-1][index-1], nodes[k-1][index], modulus[0]);
        }
      }
    }
  }
  float time_encrypt_ = time_encrypt / (double) CLOCKS_PER_SEC;
  cout<<"\n Total encryption time: "<<time_encrypt_<<endl;
  mpz_clear(temp_hash[0]);
  mpz_clear(temp_val[0]);
  return proof;
}

//===============================
// description: verifies (plaintext) Merkle tree proof or paths.
// it returns the index of rejected proofs.
vector<int> verify_proof(bigint*** proof, bigint root_node, int* challenge, int number_of_chall, int file_size, int pad_size, bigint modulus){

  int size_1 = log2(file_size) + 1;
  int tail_1, tail_2;
  bool is_in, is_in_;
  vector<int> res_;
  vector<int> vec;
  bigint* temp_hash;
  bigint one;
  mpz_init_set_str(one, "1", 10);
  temp_hash = (mpz_t*)malloc(1 * sizeof(mpz_t));
  for(int i = 0; i < number_of_chall; i++){
    for (int  j = 0; j < size_1; j++){
      if(j == 0){
        // extract the tail of the two leaf nodes
        tail_1 = extract_tail(proof[i][j][0], pad_size);
        tail_2 = extract_tail(proof[i][j+1][0], pad_size);
        // check if the tail equals the related challenge.
        is_in = search(challenge, number_of_chall, tail_1);
        is_in_ = search(challenge, number_of_chall, tail_2);
        // check if (1) either proof[i][j][0] or  proof[i][j+1][0] is the challenged block,
        // and (2) there is no duplication of proof.
        if(((is_in || is_in_) == true) && (find(vec.begin(), vec.end(), challenge[i]) == vec.end())){
          temp_hash = hash_combined_values(proof[i][j][0], proof[i][j+1][0], modulus);
          vec.push_back(challenge[i]);
        }
        else{
          res_.push_back(i); // store the index of rejected proof
          break; //exit the inner loop.
        }
        j++;
      }
      else{ // if j!=0
        if(mpz_cmp(proof[i][j][1], one) == 0){
          temp_hash = hash_combined_values(proof[i][j][0], temp_hash[0], modulus);
        }
        else{ // if mpz_cmp(proof[i][j][1], one) != 0) or when mpz_cmp(proof[i][j][1], zero) == 0
          temp_hash = hash_combined_values(temp_hash[0], proof[i][j][0], modulus);
        }
      }
      if(j+1 == size_1){
        if(mpz_cmp(temp_hash[0], root_node)!=0){
          res_.push_back(i); // store the index of rejected proof
        }
      }
    }
  }
  mpz_clear(temp_hash[0]);
  return res_;
}

//===============================
// description: checks the validity of the elements in "chall".
bool check_query(int* chall, int number_of_chall, int file_size){

  for (int i = 0; i< number_of_chall; i++){
    if(chall[i] > file_size){
      cout<<"\n There exist invalid challenge(s)"<<endl;
      return false;
    }
  }
  return true;
}

//===============================
// description: verifies only one path in the proof, given the path's index.
// it is called by the arbiter.
bool doubleCheck_proof_(bigint*** proof, bigint root_node, int* challenge, int number_of_chall, int file_size, int pad_size, int rejected_proof_index, bigint modulus){

  int size_1 = log2(file_size) + 1;
  int tail_1, tail_2;
  bool is_in, is_in_;
  bigint* temp_hash;
  bigint one;
  mpz_init_set_str(one, "1", 10);
  temp_hash = (mpz_t*)malloc(1 * sizeof(mpz_t));
  int i = rejected_proof_index;
  for (int  j = 0; j < size_1; j++){
    if(j == 0){
      // extract the tail of the two leaf nodes
      tail_1 = extract_tail(proof[i][j][0], pad_size);
      tail_2 = extract_tail(proof[i][j+1][0], pad_size);
        // check if the tail equals the related challenge.
      if(challenge[i] == tail_1 || challenge[i] == tail_2){
        temp_hash = hash_combined_values(proof[i][j][0], proof[i][j+1][0], modulus);
      }
      else{
        cout<<"\n Proof is invalid"<<endl;
        return false;
      }
      j++;
    }
    else{ // if j!=0
      if(mpz_cmp(proof[i][j][1], one) == 0){
        temp_hash = hash_combined_values(proof[i][j][0], temp_hash[0],  modulus);
      }
      else{ // if mpz_cmp(proof[i][j][1], one) != 0) or when mpz_cmp(proof[i][j][1], zero) == 0
        temp_hash = hash_combined_values(temp_hash[0], proof[i][j][0],  modulus);
      }
    }
    if(j+1 == size_1){
      if(mpz_cmp(temp_hash[0], root_node)!=0){
        cout<<"\n Proof is invalid"<<endl;
        return false;
      }
    }
  }
  mpz_clear(temp_hash[0]);
  return true;
}

//=========================
// description: generates a fresh random key.
byte* Gen_key(int key_size){

  byte* seed_;
  seed_ = new byte[key_size];
  CryptoPP::AutoSeededRandomPool prng;
  prng.GenerateBlock(seed_, key_size);
  return seed_;
}

//===============================
// description: verifies encrypted Merkle tree's proof (or paths).
// it returns the index of rejected proofs and used when the proofs need to be encrypted in the RC-PoR-P protocol.
vector<int> verify_encrypted_proof(bigint*** proof, bigint root_node, int* challenge, int number_of_chall, int file_size, int pad_size, byte* key, byte* iv, int key_size, bigint* modulus, int byte_){

  int size_1 = log2(file_size) + 1;
  int tail_1, tail_2;
  bool is_in, is_in_;
  vector<int> res_;
  vector<int> vec;
  bigint* temp_hash, * temp_val;
  bigint one;
  mpz_init_set_str(one, "1", 10);
  temp_hash = (mpz_t*)malloc(1 * sizeof(mpz_t));
  temp_val = (mpz_t*)malloc(1 * sizeof(mpz_t));
  string cipher;
  CBC_Mode< AES >::Encryption e;
	e.SetKeyWithIV(key, key_size, iv); // set the key
  for(int i = 0; i < number_of_chall; i++){
    StringSource s(to_string(i), true, new StreamTransformationFilter(e, new StringSink(cipher)));// encrypt the str_index
    unsigned char der_key_0[key_size]; // convert the ciphertext into a der_key
    memset(der_key_0, 0x00, key_size + 1);
    strcpy((char*)der_key_0, cipher.c_str());
    cipher.clear();
    for (int  j = 0; j < size_1; j++){
      if(j == 0){
        // derive a key for index j
        temp_val = encrypt(j, der_key_0, key_size, iv, byte_); // derive a key for index j
        // unblind proof[i][j][0].
        mpz_sub(temp_val[0], modulus[0], temp_val[0]);
        mpz_add(proof[i][j][0], temp_val[0], proof[i][j][0]);
        mpz_mod(proof[i][j][0], proof[i][j][0], modulus[0]);
        temp_val = encrypt(j+1, der_key_0, key_size, iv, byte_); // derive a key for index j+1
        // unblind proof[i][j+1][0].
        mpz_sub(temp_val[0], modulus[0], temp_val[0]);
        mpz_add(proof[i][j+1][0], temp_val[0], proof[i][j+1][0]);
        mpz_mod(proof[i][j+1][0], proof[i][j+1][0], modulus[0]);
        // extract the tail of the two leaf nodes
        tail_1 = extract_tail(proof[i][j][0], pad_size);
        tail_2 = extract_tail(proof[i][j+1][0], pad_size);
        // check if the tail equals the related challenge.
        is_in = search(challenge, number_of_chall, tail_1);
        is_in_ = search(challenge, number_of_chall, tail_2);
        // check if (1) either proof[i][j][0] or  proof[i][j+1][0] is the challenged block,
        // and (2) there is no duplication of proof.
        if(((is_in || is_in_) == true) && (find(vec.begin(), vec.end(), challenge[i]) == vec.end())){
          temp_hash = hash_combined_values(proof[i][j][0], proof[i][j+1][0], modulus[0]);
          vec.push_back(challenge[i]);
        }
        else{
          res_.push_back(i); // store the index of rejected proof
          break; // exit the inner loop.
        }
        j++;
      }
      else{ // if j!=0
        temp_val = encrypt(j, der_key_0, key_size, iv, byte_);//derive a key for index j
        // unblind proof[i][j][0].
        mpz_sub(temp_val[0], modulus[0], temp_val[0]);
        mpz_add(proof[i][j][0], temp_val[0], proof[i][j][0]);
        mpz_mod(proof[i][j][0], proof[i][j][0], modulus[0]);
        if(mpz_cmp(proof[i][j][1], one) == 0){
          temp_hash = hash_combined_values(proof[i][j][0], temp_hash[0], modulus[0]);
        }
        else{ // if mpz_cmp(proof[i][j][1], one) != 0) or when mpz_cmp(proof[i][j][1], zero) == 0
          temp_hash = hash_combined_values(temp_hash[0], proof[i][j][0], modulus[0]);
        }
      }
      if(j+1 == size_1){
        if(mpz_cmp(temp_hash[0], root_node)!=0){
          res_.push_back(i); // store the index of rejected proof
        }
      }
    }
  }
  mpz_clear(temp_hash[0]);
  return res_;
}

//==============================
// description: generates a fresh public key.
bigint* gen_public_key(int bit_size){

  bigint* res;
  res =  (bigint*)malloc(1 * sizeof(mpz_t));
  mpz_init(res[0]);
  Random rd;
  res = rd.gen_randSet(1, bit_size);
  mpz_nextprime(res[0], res[0]);
  return res;
}

//=====================================
// description: verifies only one path in the proof, given the path's index.
// it is used when the proofs need ot be encrypted in the protocol.
// it is called by the arbiter.
bool doubleCheck_encrypted_proof_(bigint*** proof, bigint root_node, int* challenge, int number_of_chall, int file_size, int pad_size, int rejected_proof_index, byte* key, byte* iv, int key_size, bigint* modulus, int byte_){

  int size_1 = log2(file_size) + 1;
  int tail_1, tail_2;
  bool is_in, is_in_;
  bigint* temp_hash, * temp_val;
  bigint one;
  mpz_init_set_str(one, "1", 10);
  temp_hash = (mpz_t*)malloc(1 * sizeof(mpz_t));
  temp_val = (mpz_t*)malloc(1 * sizeof(mpz_t));
  mpz_init(temp_val[0]);
  int i = rejected_proof_index;
  //----1- encrypt i
  string cipher;
  CBC_Mode< AES >::Encryption e;
	e.SetKeyWithIV(key, key_size, iv); // set the key
  StringSource s(to_string(i), true, new StreamTransformationFilter(e, new StringSink(cipher)));// encrypt the str_index
  unsigned char der_key_0[key_size]; // convert the ciphertext into a der_key
  memset(der_key_0, 0x00, key_size + 1);
  strcpy((char*)der_key_0, cipher.c_str());
  cipher.clear();
  cout<<proof[i][0][0]<<endl;
  for (int  j = 0; j < size_1; j++){
    if(j == 0){
      temp_val = encrypt(j, der_key_0, key_size, iv, byte_); //derive a key for index j
      // unblind proof[i][j][0].
      mpz_sub(temp_val[0], modulus[0], temp_val[0]);
      mpz_add(proof[i][j][0], temp_val[0], proof[i][j][0]);
      mpz_mod(proof[i][j][0], proof[i][j][0], modulus[0]);
      temp_val = encrypt(j+1, der_key_0, key_size, iv, byte_); //derive a key for index j+1
      // unblind proof[i][j+1][0].
      mpz_sub(temp_val[0], modulus[0], temp_val[0]);
      mpz_add(proof[i][j+1][0], temp_val[0], proof[i][j+1][0]);
      mpz_mod(proof[i][j+1][0], proof[i][j+1][0], modulus[0]);
      // extract the tail of the two leaf nodes
      tail_1 = extract_tail(proof[i][j][0], pad_size);
      tail_2 = extract_tail(proof[i][j+1][0], pad_size);
      // check if the tail equals the related challenge.
      if(challenge[i] == tail_1 || challenge[i] == tail_2){
        temp_hash = hash_combined_values(proof[i][j][0], proof[i][j+1][0], modulus[0]);
      }
      else{
        cout<<"\n Proof is invalid"<<endl;
        return false;
      }
      j++;
    }
    else{ // if j!=0
      temp_val = encrypt(j, der_key_0, key_size, iv, byte_); //derive a key for index j
      // unblind proof[i][j][0].
      mpz_sub(temp_val[0], modulus[0], temp_val[0]);
      mpz_add(proof[i][j][0], temp_val[0], proof[i][j][0]);
      mpz_mod(proof[i][j][0], proof[i][j][0], modulus[0]);
      if(mpz_cmp(proof[i][j][1], one) == 0){
        temp_hash = hash_combined_values(proof[i][j][0], temp_hash[0],  modulus[0]);
      }
      else{ // if mpz_cmp(proof[i][j][1], one) != 0) or when mpz_cmp(proof[i][j][1], zero) == 0
        temp_hash = hash_combined_values(temp_hash[0], proof[i][j][0],  modulus[0]);
      }
    }
    if(j+1 == size_1){
      if(mpz_cmp(temp_hash[0], root_node)!=0){
        cout<<"\n Proof is invalid"<<endl;
        return false;
      }
    }
  }
  mpz_clear(temp_hash[0]);
  return true;
}

//===============================
int main() {
  bigint* file;
  bigint test_,root_, root_s;
  bigint** nodes, **nodes_;
  int file_size = 1048576; // 2^20=1048576, 2^22 = 4194304,   2^23 = 8388608 , 2^24 = 16777216,  2^25= 33554432, 2^26 = 67108864,  number of blocks
  string binary_fileSize = toBinary(file_size);
  int pad_size = binary_fileSize.length()+1;
  int block_bit_size = 80;
  int number_of_levels = log2(file_size);
  int number_of_chall = 460;
  int bit_size_of_chall = 50;
  int int_modulus = file_size;
  int public_key_size = 128;
  int rejected_proof_index;
  file = (bigint*)malloc(file_size * sizeof(bigint));
  Random rd_;
  // Genenerate a random file
  file = rd_.gen_randSet(file_size, block_bit_size);
  /////////// Thefollowing steps are off-chain algorithms of RC-PoR-P.
  //// 1- Key Generation
  cout<<"\n file_size: "<<file_size<<endl;
  double client_setup;
  double start_client_setup = clock();
  cout<<"\n-----1- Generates a fresh key for the pseudorandom function-----"<<endl;
  int key_size = AES::DEFAULT_KEYLENGTH;
  int block_size = AES::BLOCKSIZE;
  bigint* modulus;
  byte* seed;
  byte* iv;
  // generate seed_ and iv;
  seed = Gen_key(key_size); // seed: master seed for PRF
  iv = Gen_key(block_size); // iv for PRF
  modulus = gen_public_key(public_key_size);
  //////////////////////////////////////////////
  //// 2- Client-side Initiation
  cout<<"\n-------2- Client-side Initiation-----------"<<endl;
  cout<<"\n a- Encoding the file"<<endl;
  bigint* encoded_file = encode_file(file, file_size, pad_size);
  // 2.1- build a Merkle tree on the encoded file.
  cout<<"\n b- Building a tree on the file"<<endl;
  nodes = build_MT_tree(encoded_file, file_size, modulus[0]);
  // 2.2- extract the root
  mpz_init_set(root_, nodes[number_of_levels - 1][0]);
  double end_client_setup = clock();
  client_setup = end_client_setup - start_client_setup;
  float client_setup_ = client_setup / (double) CLOCKS_PER_SEC;
  cout<<"\n client_side_init: "<<client_setup_<<endl;
  ///////////////////////////////////////////////////
  //// 3- Server-side Initiation
  cout<<"\n-----3- Server-side Initiation-----"<<endl;
  // PoRID.serve
  // 3.a- build a Merkle tree on the encoded file.
  cout<<"\n Building a tree on the file"<<endl;
  double start_server_init = clock();
  nodes_ = build_MT_tree(encoded_file, file_size, modulus[0]);
  // 3.b- extract the root of the tree
  mpz_init_set(root_s, nodes_[number_of_levels - 1][0]);
  // 3.c- compare the two roots (i.e., the one it generated with the root generated by the  client)
  if (mpz_cmp(root_, root_s)!= 0){
    cout<<"\n The serve will no serve due to an invalid root provided"<<endl;
    return 0;
  }
  double end_server_init = clock();
  double server_init = end_server_init - start_server_init;
  float server_init_ = server_init / (double) CLOCKS_PER_SEC;
  cout<<"\n server_side_init: "<<server_init_<<endl;
  ///////////////////////////////////////////////////
  //// 4- Client-side Query Generation.
  double start_client_genQuery = clock();
  cout<<"\n-----4- Client-side Query Generation-----"<<endl;
  int* chall = gen_chall_(number_of_chall, bit_size_of_chall, int_modulus);
  double end_client_genQuery  = clock();
  double client_genQuery = end_client_genQuery - start_client_genQuery;
  float client_genQuery_ = client_genQuery / (double) CLOCKS_PER_SEC;
  cout<<"\n client_genQuery: "<<client_genQuery_<<endl;
  ///////////////////////////////////////////////////
  //// 5- Server-side Proof Generation
  cout<<"\n-----5- Server-side Proof Generation-----"<<endl;
  // 5.1. check query
  cout<<"\n a- verify query-----"<<endl;
  double start_server_genProof = clock();
  bool check_q = check_query(chall, number_of_chall, file_size);
  if (!check_q){
    cout<<"\n The server will not serve due to invalid queries provided"<<endl;
    return 0;
  }
  cout<<"\n b- generate a proof-----"<<endl;
  int byte =(public_key_size)/8 ;
  bigint***proof_= gen_encrypted_proof(number_of_chall, chall, encoded_file, file_size, nodes, seed, iv, key_size, modulus, byte);
  double end_server_genProof = clock();
  double server_genProof = end_server_genProof - start_server_genProof;
  float server_genProof_ = server_genProof / (double) CLOCKS_PER_SEC;
  cout<<"\n server_genProof: "<<server_genProof_<<endl;//***
  ///////////////////////////////////////////////////
  //// 6- verify valid proofs
  cout<<"\n-----Verify proofs-----"<<endl;
  //--------Comment this out to see the result of an invalid proof and how the arbiter reacts
  // bigint one;
  // mpz_init_set_str(one, "4564564654564654456",10);
  // mpz_set(proof_[0][0][0],one);
  //-------------------
  double start_client_verProof = clock();
  vector<int>vec_ = verify_encrypted_proof(proof_, root_, chall, number_of_chall, file_size, pad_size, seed, iv, key_size, modulus, byte);
  string status;
  if(vec_.size() == 0){
    status = "All proofs are VALID";
  }
  else{
    status = "Some proofs are INVALID";
  }
  cout<<"\n\n------------"<<endl;
  cout<< "\n Status: "<<status<<endl;
  int temp_counter = 0;
  if (status == "Some proofs are INVALID"){
    for(int i = 0; i < vec_.size(); i++){
      cout<<"\n Rejected proof index:"<<vec_[i]<<endl;
      // store firt rejected proof's index
      if(temp_counter == 0){
        rejected_proof_index = vec_[i];
        temp_counter++;
      }
    }
  }
  double end_client_verProof = clock();
  double client_verProof = end_client_verProof - start_client_verProof;
  float client_verProof_ = client_verProof / (double) CLOCKS_PER_SEC;
  cout<<"\n client_verProof: "<<client_verProof_<<endl;//***
  ////////////////////////////////
  //// 7- Identify
  cout<<"\n\n------Identify a misbehaving party------"<<endl;
  double start_arbiter_identify = clock();
  //high_resolution_clock::time_point t1 = high_resolution_clock::now();
  bool detected = false;
  // 7.a. Verify Query
  bool check_q_ = check_query(chall, number_of_chall, file_size);
  if (!check_q_){
    cout<<"\n The query has been rejected by the Auditor-So the Client is malicious"<<endl;
    detected = true;
    return 0;
  }
  // 7.b. Check a certain proof, given rejected_proof_index.
  if(vec_.size() != 0){
  bool double_check = doubleCheck_encrypted_proof_(proof_, root_, chall, number_of_chall, file_size, pad_size, rejected_proof_index, seed, iv, key_size, modulus, byte);
  // bool double_check = doubleCheck_proof_(proof_, root_, chall, number_of_chall, file_size, pad_size, rejected_proof_index, modulus);
  double end_arbiter_identify = clock();
  double arbiter_identify = end_arbiter_identify - start_arbiter_identify;
  float arbiter_identify_ = arbiter_identify / (double) CLOCKS_PER_SEC;
  cout<<"\n arbiter_identify: "<<arbiter_identify_<<endl;
  if (!double_check){
    cout<<"\n Proof has been rejected by the Auditor--So the Server is malicious"<<endl;
    detected = true;
  }}
  if (!detected){
    cout<<"\n No misbehaviour was detected"<<endl;
  }
  cout<<"-------------------"<<endl;
  cout<<endl;
  return 0;
}
