(**********************************************************************
    Proof of Huffman algorithm: Extraction.v                         
                                                                     
    Extraction for the huffman algorithm                             
                                                                     
    Create a file huffman.ml where the function huffman is the       
    algorithm                                                        
                                                                     
                                    Laurent.Thery@inria.fr (2003)    
  **********************************************************************)
Require Import Huffman.
Require Import Code.
Require Import ISort.
 
Extraction Inline list_length_induction.
Extraction
 NoInline code insert isort map frequency_list huffman encode decode.
 
 
Extraction "huffman.ml" code huffman encode decode.