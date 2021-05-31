//

#include <iostream>
#include <math.h>
#include <string>
#include <stdio.h>
#include <stdlib.h>
#include "cryptopp/cryptlib.h"
#include "cryptopp/sha.h"
#include "cryptopp/filters.h"
#include "cryptopp/hex.h"
#include "cryptopp/secblock.h"
#include "gmp.h"
#include <gmpxx.h>
#include "Rand.h"
using namespace std;
using namespace CryptoPP;
typedef mpz_t bigint;



// description: given values a and b, it returns hash(a||b)
bigint* hash_combined_values(bigint val_1, bigint val_2){
  string s_val_1, s_val_2, s_val_com;
  CryptoPP::SHA256 hash2;
  byte digest[CryptoPP::SHA256::DIGESTSIZE];
  bigint* res;
  res = (bigint*)malloc(1 * sizeof(bigint));
  s_val_1 = mpz_get_str(NULL, 10,  val_1);
  s_val_2 = mpz_get_str(NULL, 10, val_2);
  s_val_com = s_val_1 + s_val_2;
  unsigned int nDataLen = s_val_com.length();
  hash2.CalculateDigest(digest, (byte*)s_val_com.c_str(), nDataLen);
  s_val_com.clear();
  s_val_1.clear();
  s_val_2.clear();
  mpz_init(res[0]);
  mpz_import(res[0], sizeof(digest), 1, sizeof(digest[0]), 0, 0, digest);
  return res;
}



bigint** build_MT_tree(bigint* file, int file_size){

    int number_of_levels = log2(file_size);// number of levels excluding leaf nodes level
    //cout<<"\n number_of_levels"<<number_of_levels<<endl;
    bigint** nodes;
    nodes = (bigint**)malloc(number_of_levels * sizeof(bigint));// initiate a 2-D array
    int temp_size_1;
    for (int i = 0; i < number_of_levels; i++){
        temp_size_1 = file_size/(pow(2,i+1));//number of nodes in each level starting from one level up the leaf nodes
        nodes[i] = (mpz_t*)malloc(temp_size_1 * sizeof(mpz_t));// initiate each array
    }
    CryptoPP::SHA256 hash2;
    byte digest[CryptoPP::SHA256::DIGESTSIZE];

    for (int  k = 0; k < number_of_levels; k++){

        int j = 0;
        string s_val_1, s_val_2, s_val_com;
        int temp_size_2 = file_size/(pow(2,k));
        for(int i = 0; i < temp_size_2;){

            if(k == 0){
                bigint* res_= hash_combined_values(file[i],file[i+1]);
                mpz_set(nodes[k][j],res_[0]);
                j++;
                i += 2;
            }
            else{
                bigint* res_= hash_combined_values(nodes[k-1][i],nodes[k-1][i+1]);
                mpz_set(nodes[k][j],res_[0]);
                j++;
                i += 2;
            }
        }
    }
    return nodes;
}


int* gen_chall(int number_of_chall, int bit_size_of_chall, int int_modulus){

    Random rd_;
    int* ar;
    ar= new int[number_of_chall];
    bigint* set, bigint_modulus;
    set = (bigint*)malloc(number_of_chall * sizeof(bigint));
    set = rd_.gen_randSet(number_of_chall, bit_size_of_chall);// generate a set of random bigint
    // put them in the range: [0,int_modulus-1]
    mpz_init(bigint_modulus);
    mpz_set_ui(bigint_modulus, int_modulus);
    for (int i = 0; i < number_of_chall; i++){
      mpz_mod(set[i], set[i], bigint_modulus);
      ar[i] = mpz_get_ui(set[i]);
    }
    return ar;
}



int find_index(bigint* set, int set_size, bigint val,bool &res_){

  int res;
  for(int i = 0; i < set_size; i++){
    if (mpz_cmp(set[i], val) == 0){
      res_ = true;
      return i;// 0 means val exists in the set
    }
  }
  res_ = false;
  return 0;
}


bigint*** gen_proof(int number_of_chall, int* challenge, bigint* file, int file_size, bigint** nodes){

  bigint*** proof;
  int size_1 = log2(file_size) + 2; //number of elements in each proof (related to each challenge)
  //cout<<"\n size_1:"<<size_1<<endl;
  proof = (bigint***)malloc(number_of_chall * sizeof(bigint));
  int number_of_levels = log2(file_size) + 1;// number of levels in the tree including leaf nodes
  //cout<<"\n number_of_levels:"<<number_of_levels<<endl;
  //cout<<"\n in gen_proof--number_of_levels:"<<number_of_levels<<endl;
  bigint* temp_hash;
  temp_hash = (mpz_t*)malloc(1 * sizeof(mpz_t));

  for(int i = 0; i < number_of_chall; i++){

    proof[i] = (bigint**)malloc(size_1 * sizeof(bigint));
    for(int t = 0; t < size_1; t++){
      proof[i][t] = (bigint*)malloc(2 * sizeof(bigint));
    }
    //go through different levels of the tree including leaf nodes
    int j = 0;
    for (int  k = 0; k < number_of_levels; k++){
      //cout<<"\n in gen_proof--k:"<<k<<endl;

      if(k == 0){
        if(challenge[i] % 2 == 0){ // if challenge[i] (or the index of challenged file block) is even
          mpz_init_set(proof[i][j][0], file[challenge[i]]); // insert leaf node file[challenge[i]] to the proof
          mpz_init_set_str(proof[i][j][1], "0", 10);
          //cout<<"\n in gen_proof--k==0--proof["<<i<<"]["<<j<<"][0]: "<<proof[i][j][0]<<endl;
          j++;
          mpz_init_set(proof[i][j][0], file[challenge[i] + 1]); // insert the next leaf node file: [challenge[i]] to the proof
          mpz_init_set_str(proof[i][j][1], "0", 10);
          //cout<<"\n in gen_proof--k==0--proof["<<i<<"]["<<j<<"][0]: "<<proof[i][j][0]<<endl;
          j++;
        // generate hash(file[challenge[i]] ||file[challenge[i]+1])
          temp_hash = hash_combined_values(file[challenge[i]],file[challenge[i] + 1]);
        }
        else{ // if challenge[i] is odd
          mpz_init_set(proof[i][j][0], file[challenge[i]-1]); // insert leaf node file[challenge[i]] to the proof
          mpz_init_set_str(proof[i][j][1], "0", 10);
          //cout<<"\n in gen_proof--k==0--proof["<<i<<"]["<<j<<"][0]: "<<proof[i][j][0]<<endl;
          j++;
          mpz_init_set(proof[i][j][0], file[challenge[i]]); // insert the next leaf node file: [challenge[i]] to the proof
          mpz_init_set_str(proof[i][j][1], "0", 10);
          //cout<<"\n in gen_proof--k==0--proof["<<i<<"]["<<j<<"][0]: "<<proof[i][j][0]<<endl;
          j++;
          temp_hash = hash_combined_values(file[challenge[i]-1], file[challenge[i]]);
          //cout<<"\n in k=0--k: "<<k<<", temp_hash: "<<temp_hash[0]<<endl;
        }
      }
      else{ // if k is not zero
        // find the index of temp_hash in the next level node
        //cout<<"\n in k!=0--k: "<<k<<", temp_hash: "<<temp_hash[0]<<endl;
        int nonil = file_size/(pow(2,k));//nonil: number_of_nodes_inEach_level
        bool res_;
        int index = find_index(nodes[k-1], nonil, temp_hash[0], res_);// find the index of temp_hash in nodes[k-1]
        //cout<<"\n index-k!=0----k: "<<k<<", index:" <<index<<endl;
        if(index % 2 == 0 && res_){

          if(index == 0 && k+1 == number_of_levels){
            //cout<<"in the root node"<<endl;
            mpz_init_set(proof[i][j][0], nodes[k-1][index]);
            //cout<<"in the root node----proof["<<i<<"]["<<j<<"][0]: "<<proof[i][j][0]<<endl;
            mpz_init_set_str(proof[i][j][1], "0", 10);

          }
          else{

          mpz_init_set(proof[i][j][0], nodes[k-1][index+1]);
          mpz_init_set_str(proof[i][j][1], "0", 10);
          //cout<<"\n in gen_proof--k!=0--proof["<<i<<"]["<<j<<"][0]: "<<proof[i][j][0]<<endl;
          j++;
          temp_hash = hash_combined_values(nodes[k-1][index], nodes[k-1][index+1]);
          //cout<<"\n in gen_proof--k!=0--temp_hash: "<<temp_hash[0]<<endl;
        }

        }
        else if(index % 2 != 0 && res_){
          mpz_init_set(proof[i][j][0], nodes[k-1][index-1]);
          mpz_init_set_str(proof[i][j][1], "1", 10);
          //cout<<"\n in gen_proof--k!=0--proof["<<i<<"]["<<j<<"][0]: "<<proof[i][j][0]<<endl;
          j++;
          temp_hash = hash_combined_values(nodes[k-1][index-1], nodes[k-1][index]);
        }
      }
    }
  }
  return proof;
}

//int number_of_chall
 //int file_size
bool verify_proof(bigint*** proofs, bigint root_node, int* challenge, int number_of_chall, int file_size){
  // int number_of_levels = log2(file_size) + 1;
  // int size_1 = log2(file_size) + 2;
  //1- check the roots in all proofs equal root_node.
  /* 2-
    for(int i = 0; i < number_of_chall; i++){

      for (int  j = 0; j < size_1; j++){



      }
*/
  bool res;



  return res;
}



// bigint** gen_proof(int number_of_chall, int* challenge, bigint* file, int file_size, bigint** nodes){
//
//   bigint** proof;
//   int size_1 = log2(file_size) + 2; //number of elements in each proof (related to each challenge)
//   proof = (bigint**)malloc(number_of_chall * sizeof(bigint));
//   int number_of_levels = log2(file_size) + 1;// number of levels in the tree including leaf nodes
//   bigint* temp_hash;
//   temp_hash = (mpz_t*)malloc(1 * sizeof(mpz_t));
//
//   for(int i = 0; i < number_of_chall; i++){
//
//     proof[i] = (bigint*)malloc(size_1 * sizeof(bigint));
//     //go through different levels of the tree including leaf nodes
//     for (int  k = 0; k < number_of_levels; k++){
//
//       int j = 0;
//       if(k == 0){
//         if(challenge[i] % 2 == 0){ // if challenge[i] (or the index of challenged file block) is even
//           mpz_init_set(proof[i][j], file[challenge[i]]); // insert leaf node file[challenge[i]] to the proof
//           j++;
//           mpz_init_set(proof[i][j], file[challenge[i] + 1]); // insert the next leaf node file: [challenge[i]] to the proof
//           j++;
//         // generate hash(file[challenge[i]] ||file[challenge[i]+1])
//           temp_hash = hash_combined_values(file[challenge[i]],file[challenge[i] + 1]);
//         }
//         else{ // if challenge[i] is odd
//           mpz_init_set(proof[i][j], file[challenge[i]-1]); // insert leaf node file[challenge[i]] to the proof
//           j++;
//           mpz_init_set(proof[i][j], file[challenge[i]]); // insert the next leaf node file: [challenge[i]] to the proof
//           j++;
//           temp_hash = hash_combined_values(file[challenge[i]-1], file[challenge[i]]);
//         }
//       }
//       else{ // if k is not zero
//         // find the index of temp_hash in the next level node
//         int nonil = file_size/(pow(2,k));//nonil: number_of_nodes_inEach_level
//         bool res_;
//         int index = find_index(nodes[k-1], nonil, temp_hash[0], res_);// find the index of temp_hash in nodes[k-1]
//         if(index % 2 == 0 && res_){
//           mpz_init_set(proof[i][j], nodes[k-1][index+1]);
//           j++;
//           temp_hash = hash_combined_values(nodes[k-1][index], nodes[k-1][index+1]);
//         }
//         else if(index % 2 != 0 && res_){
//           mpz_init_set(proof[i][j], nodes[k-1][index-1]);
//           j++;
//           temp_hash = hash_combined_values(nodes[k-1][index-1], nodes[k-1][index]);
//         }
//       }
//     }
//   }
// }




int main() {

    bigint* file;
    bigint test_;
    int file_size = 8;
    file = (bigint*)malloc(file_size * sizeof(bigint));

    mpz_init_set_str(file[0], "5", 10);
    mpz_init_set_str(file[1], "6", 10);
    mpz_init_set_str(file[2], "7", 10);
    mpz_init_set_str(file[3], "8", 10);
    mpz_init_set_str(file[4], "9", 10);
    mpz_init_set_str(file[5], "10", 10);
    mpz_init_set_str(file[6], "11", 10);
    mpz_init_set_str(file[7], "12", 10);

    //cout<<file[0]<<"---"<<file[1]<<endl;
    // mpz_init_set_str(test_, "555", 10);
    bigint** res;
    res = build_MT_tree(file, file_size);

    //----------gen_random chalenges.

    int number_of_chall = 5;
    int bit_size_of_chall = 80;
    int int_modulus = 8;
    cout<<"\n============="<<endl;
    int* rand_set = gen_chall( number_of_chall, bit_size_of_chall, int_modulus);

    for (int i=0; i< number_of_chall; i++){
        cout<<"\n challnege elmeents: " <<rand_set[i]<<endl;
    }
    bool res_;
    cout<<"\n============="<<endl;

bigint*** proof_= gen_proof(number_of_chall, rand_set, file, file_size, res);
int size_1 = log2(file_size) + 2;//number of elements in each proof (related to each challenge)
  int number_of_levels = log2(file_size) + 1;//number of elements in each proof
cout<<"\n size_1: "<<size_1<<endl;

for(int i=0;i < number_of_chall; i++){
  cout<<"\n\n ******************"<<endl;
  for(int j=0;j < size_1; j++){
    cout<<"\n proof_["<<i<<"]["<<j<<"][0]: "<<proof_[i][j][0]<<endl;
    cout<<"\n proof_["<<i<<"]["<<j<<"][1]: "<<proof_[i][j][1]<<endl;
  }

}
    // int index = find_index(file, file_size, test_, res_);
    // cout<<"\n test find_index, bool:"<<res_<<", index: "<<index<<endl;


    //--------------



    /*
    cout<<"\n-----------"<<endl;
    cout<<res[0][0]<<endl;
    cout<<"\n-----------"<<endl;
    cout<<res[0][1]<<endl;
    cout<<"\n-----------"<<endl;
    cout<<res[1][0]<<endl;
    cout<<"\n-----------"<<endl;
    cout<<res[1][1]<<endl;
    cout<<"\n-----------"<<endl;
     */
     // bigint*** proof;
     // int size_1=5;//number_of_chall
     // int size_2= 4;//proof_size
     // int size_3=2;//
     // proof = (bigint***)malloc(size_1 * sizeof(bigint));
     //
     // for(int i = 0; i < size_1; i++){
     //   proof[i] = (bigint**)malloc(size_2 * sizeof(bigint));
     //   for(int t = 0; t < size_2; t++){
     //      proof[i][t] = (bigint*)malloc(size_3 * sizeof(bigint));
     //      mpz_init_set(proof[i][t][0], file[t]);
     //      mpz_init_set_str(proof[i][t][1], "11", 10);
     //    }
     //  }
     //  for(int i = 0; i < size_1; i++){
     //    for(int t = 0; t < size_2; t++){
     //       cout<<"\n\n proof["<<i<<"]["<<t<<"][0]:"<<proof[i][t][0]<<endl;
     //       cout<<"\n\n proof["<<i<<"]["<<t<<"][1]:"<<proof[i][t][1]<<endl;
     //     }
     //   }


    return 0;
}
