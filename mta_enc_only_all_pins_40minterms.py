#
import math 
from itertools import combinations
import bitwuzla
import random
import time


BITSi = 7
BITSo = 8
ROWS=2**BITSi

ENC_GATES = 40
DEC_GATES = 40

# define bit vector sorts for encoder value and decoder value 
bv_sort_BITSo = bitwuzla.mk_bv_sort(BITSo)
bv_sort_BITSi = bitwuzla.mk_bv_sort(BITSi)


# sort for total gate 
bv_sort_enc_gate =  bitwuzla.mk_bv_sort(ENC_GATES)
bv_sort_dec_gate =  bitwuzla.mk_bv_sort(DEC_GATES)

# Bitwuzla options 
options = bitwuzla.Options()
options.set(bitwuzla.Option.PRODUCE_MODELS, True)
options.set(bitwuzla.Option.VERBOSITY, 4)
#options.set(bitwuzla.Option.BV_SOLVER, 'prop')
#options.set(bitwuzla.Option.LOGLEVEL,2)
options.set(bitwuzla.Option.PP_ELIM_BV_EXTRACTS, True)
#options.set(bitwuzla.Option.SAT_SOLVER, 'kissat')
#options.set(bitwuzla.Option.SEED, 22)
#options.set(bitwuzla.Option.MEMORY_LIMIT,16384)

bitwuzla_solver = bitwuzla.Bitwuzla(options)

# Creating an array of bit-vector variables
code = [bitwuzla.mk_const(bv_sort_BITSo, 'code_%d' % r) for r in range(ROWS)]  # Ensure ROWS is defined

# Gate minterm bit vectors (0/1)
enc_position_bvs = [bitwuzla.mk_const(bv_sort_BITSi,f'enc_pos_{i}') for i in range(ENC_GATES)]
dec_position_bvs = [bitwuzla.mk_const(bv_sort_BITSo,f'dec_pos_{i}') for i in range(DEC_GATES)]

# Gate dont' care (DC) bit vectors - separate out trial to see if ordering is easier 
enc_dc_bvs = [bitwuzla.mk_const(bv_sort_BITSi,f'enc_pos_{i}') for i in range(ENC_GATES)]
dec_dc_bvs = [bitwuzla.mk_const(bv_sort_BITSo,f'dec_pos_{i}') for i in range(DEC_GATES)]

# minterm enable per pin
enc_gate_enable = [bitwuzla.mk_const(bv_sort_enc_gate, 'enc_gate_en_%d' % r) for r in range(BITSo)] 
dec_gate_enable = [bitwuzla.mk_const(bv_sort_dec_gate, 'dec_gate_en_%d' % r) for r in range(BITSi)]  

# Create a constantbit-vectors
zero_val = bitwuzla.mk_bv_value(bitwuzla.mk_bv_sort(1), "0", 2)
one_val = bitwuzla.mk_bv_value(bitwuzla.mk_bv_sort(1), "1", 2)

enc_one_val = bitwuzla.mk_bv_value(bitwuzla.mk_bv_sort(BITSi), "1", 2)
dec_one_val = bitwuzla.mk_bv_value(bitwuzla.mk_bv_sort(BITSo), "1", 2)

# Go through each code assignment case (2**BITSi)
for lcv in range(ROWS):
    print('loop iter is ' + str(lcv),flush=True)

    # Convert i to binary and update x variables as regular Python booleans
    binary_i = format(lcv, '07b')
    x = [binary_i[j] == '1' for j in range(BITSi)]

    # Assuming x is a list of booleans
    binary_str = ''.join(['1' if bit else '0' for bit in x])

    # Convert the binary string to a bit vector in Bitwuzla
    xbv = bitwuzla.mk_bv_value(bitwuzla.mk_bv_sort(7), binary_str, 2)


    # Extract bits
    code_lcv = bitwuzla.mk_term(bitwuzla.Kind.BV_EXTRACT, [code[lcv]],[BITSo-1,0]) 
   
    # Slice bits for individual bit constraints later 
    bit0 = bitwuzla.mk_term(bitwuzla.Kind.BV_EXTRACT, [code[lcv]],[0,0]) 
    bit1 = bitwuzla.mk_term(bitwuzla.Kind.BV_EXTRACT, [code[lcv]],[1,1])
    bit2 = bitwuzla.mk_term(bitwuzla.Kind.BV_EXTRACT, [code[lcv]],[2,2]) 
    bit3 = bitwuzla.mk_term(bitwuzla.Kind.BV_EXTRACT, [code[lcv]],[3,3])
    bit4 = bitwuzla.mk_term(bitwuzla.Kind.BV_EXTRACT, [code[lcv]],[4,4]) 
    bit5 = bitwuzla.mk_term(bitwuzla.Kind.BV_EXTRACT, [code[lcv]],[5,5])
    bit6 = bitwuzla.mk_term(bitwuzla.Kind.BV_EXTRACT, [code[lcv]],[6,6]) 
    bit7 = bitwuzla.mk_term(bitwuzla.Kind.BV_EXTRACT, [code[lcv]],[7,7])    

    bits = [bit0, bit1, bit2, bit3, bit4, bit5, bit6, bit7]

    # Add MTA constraints - first geneate negations (don't think bitwise python operations work)
    not_bit0 = bitwuzla.mk_term(bitwuzla.Kind.BV_NOT, [bit0])
    not_bit1 = bitwuzla.mk_term(bitwuzla.Kind.BV_NOT, [bit1])
    not_bit2 = bitwuzla.mk_term(bitwuzla.Kind.BV_NOT, [bit2])
    not_bit3 = bitwuzla.mk_term(bitwuzla.Kind.BV_NOT, [bit3])
    not_bit4 = bitwuzla.mk_term(bitwuzla.Kind.BV_NOT, [bit4])
    not_bit5 = bitwuzla.mk_term(bitwuzla.Kind.BV_NOT, [bit5])
    not_bit6 = bitwuzla.mk_term(bitwuzla.Kind.BV_NOT, [bit6])
    not_bit7 = bitwuzla.mk_term(bitwuzla.Kind.BV_NOT, [bit7])
     
    not_bits = [not_bit0, not_bit1, not_bit2, not_bit3, not_bit4, not_bit5, not_bit6, not_bit7]

    '''
    # Focus on Decoder first - generate / extract gate information 
    dec_minterms = []        
    for j in range(DEC_GATES):

        # get the location value positions (invert/don't invert)
        val_lcv = bitwuzla.mk_term(bitwuzla.Kind.BV_EXTRACT, [dec_position_bvs[j]],[BITSo-1,0]) 

        # get the location dont care positions (1 means dont include in final minterm)
        dec_dc_lcv = bitwuzla.mk_term(bitwuzla.Kind.BV_EXTRACT, [dec_dc_bvs[j]],[BITSo-1,0]) 

        #code_lcv is defined to be bitwuzla.mk_term(bitwuzla.Kind.BV_EXTRACT, [code[lcv]],[0,BITSo-1]) 

        # apply bit wise XOR between val_lcv and code_lcv
        code_lcv_xor = bitwuzla.mk_term(bitwuzla.Kind.BV_XOR, [code_lcv, val_lcv])

        # OR result of code_lcv_xor and dec_dc_lv to get final result 
        code_lcv_xor_dc = bitwuzla.mk_term(bitwuzla.Kind.BV_OR, [code_lcv_xor, dec_dc_lcv])

        # check value (1111111)
        bit_check = bitwuzla.mk_term(bitwuzla.Kind.EQUAL, [code_lcv_xor_dc, dec_one_val])

        ## now need to do AND across bits 
        minterm = one_val 
        for k in range(BITSo):
            # Extract each bit and check if 
            bit = bitwuzla.mk_term(bitwuzla.Kind.BV_EXTRACT, [code_lcv_xor_dc], [k, k])
            minterm =  bitwuzla.mk_term(bitwuzla.Kind.BV_AND, [minterm, bit])

        # finally append minterm (1-bit bit vector to list)
        dec_minterms.append(minterm)

        if j < DEC_GATES-1:
            #bitwuzla_solver.assert_formula(bitwuzla.mk_term(bitwuzla.Kind.BV_UGE, [dec_position_bvs[j+1], dec_position_bvs[j]]))
            bitwuzla_solver.assert_formula(bitwuzla.mk_term(bitwuzla.Kind.BV_UGE, [dec_dc_bvs[j+1], dec_dc_bvs[j]]))

    # now go through pins and form sop
    for z in range(BITSi):
        minterm_sop = zero_val

        for j in range(DEC_GATES):
            # now perform AND with enable at position GATE
            extracted_enable = bitwuzla.mk_term(bitwuzla.Kind.BV_EXTRACT, [dec_gate_enable[z]],[j,j]) 
            minterm_res = bitwuzla.mk_term(bitwuzla.Kind.BV_AND,[dec_minterms[j], extracted_enable])

            # now perform OR operation with minterm_sop
            minterm_sop = bitwuzla.mk_term(bitwuzla.Kind.BV_OR, [minterm_res, minterm_sop])
        
        # for current codeword, set equal to decoder logic circuit output
        decode_equality_term = bitwuzla.mk_term(
            bitwuzla.Kind.EQUAL, 
            [bitwuzla.mk_bv_value(bitwuzla.mk_bv_sort(1), "1" if x[z] else "0", 2), minterm_sop]
        )
        bitwuzla_solver.assert_formula(decode_equality_term)
    
    '''

    # Focus on Decoder first - generate / extract gate information 
    enc_minterms = []        
    for j in range(ENC_GATES):

        # get the location value positions (invert/don't invert)
        val_lcv = bitwuzla.mk_term(bitwuzla.Kind.BV_EXTRACT, [enc_position_bvs[j]],[BITSi-1,0]) 

        # get the location dont care positions (1 means dont include in final minterm)
        enc_dc_lcv = bitwuzla.mk_term(bitwuzla.Kind.BV_EXTRACT, [enc_dc_bvs[j]],[BITSi-1,0]) 

        #code_lcv is defined to be bitwuzla.mk_term(bitwuzla.Kind.BV_EXTRACT, [code[lcv]],[0,BITSo-1]) 

        # apply bit wise XOR between val_lcv and code_lcv
        code_lcv_xor = bitwuzla.mk_term(bitwuzla.Kind.BV_XOR, [xbv, val_lcv])

        # OR result of code_lcv_xor and dec_dc_lv to get final result 
        code_lcv_xor_dc = bitwuzla.mk_term(bitwuzla.Kind.BV_OR, [code_lcv_xor, enc_dc_lcv])

        # check value (1111111)
        bit_check = bitwuzla.mk_term(bitwuzla.Kind.EQUAL, [code_lcv_xor_dc, enc_one_val])

        ## now need to do AND across bits 
        minterm = one_val 
        for k in range(BITSi):
            # Extract each bit and check if 
            bit = bitwuzla.mk_term(bitwuzla.Kind.BV_EXTRACT, [code_lcv_xor_dc], [k, k])
            minterm =  bitwuzla.mk_term(bitwuzla.Kind.BV_AND, [minterm, bit])

        # finally append minterm (1-bit bit vector to list)
        enc_minterms.append(minterm)
        if j < ENC_GATES-1:
            #bitwuzla_solver.assert_formula(bitwuzla.mk_term(bitwuzla.Kind.BV_UGE, [enc_position_bvs[j+1], enc_position_bvs[j]]))
            bitwuzla_solver.assert_formula(bitwuzla.mk_term(bitwuzla.Kind.BV_ULE, [enc_dc_bvs[j+1], enc_dc_bvs[j]]))

    # now go through pins and form sop
    for z in range(BITSo):
        minterm_sop = zero_val

        for j in range(ENC_GATES):
            # now perform AND with enable at position GATE
            extracted_enable = bitwuzla.mk_term(bitwuzla.Kind.BV_EXTRACT, [enc_gate_enable[z]],[j,j]) 
            minterm_res = bitwuzla.mk_term(bitwuzla.Kind.BV_AND,[enc_minterms[j], extracted_enable])

            # now perform OR operation with minterm_sop
            minterm_sop = bitwuzla.mk_term(bitwuzla.Kind.BV_OR, [minterm_res, minterm_sop])        

        # for current codeword, set equal to decoder logic circuit output
        encode_equality_term = bitwuzla.mk_term(
            bitwuzla.Kind.EQUAL, 
            [bits[z], minterm_sop]
        )
        bitwuzla_solver.assert_formula(encode_equality_term)
    


        
    # Create the AND operations
    s0_0 = bitwuzla.mk_term(bitwuzla.Kind.BV_AND, [bit1,not_bit0])
    s1_3 = bitwuzla.mk_term(bitwuzla.Kind.BV_AND, [not_bit2, not_bit3])
    s1_0 = bitwuzla.mk_term(bitwuzla.Kind.BV_AND, [bit3, not_bit2])
    s0_3 = bitwuzla.mk_term(bitwuzla.Kind.BV_AND, [not_bit0, not_bit1])

    s1_0 = bitwuzla.mk_term(bitwuzla.Kind.BV_AND, [bit3, not_bit2])
    s2_3 = bitwuzla.mk_term(bitwuzla.Kind.BV_AND, [not_bit4, not_bit5])
    s2_0 = bitwuzla.mk_term(bitwuzla.Kind.BV_AND, [bit5, not_bit4])
    s1_3 = bitwuzla.mk_term(bitwuzla.Kind.BV_AND, [not_bit2, not_bit3])

    s2_0 = bitwuzla.mk_term(bitwuzla.Kind.BV_AND, [bit5, not_bit4])
    s3_3 = bitwuzla.mk_term(bitwuzla.Kind.BV_AND, [not_bit6, not_bit7])
    #s3_0 = bitwuzla.mk_term(bitwuzla.Kind.BV_AND, [bit7, bit6])
    #s2_3 = bitwuzla.mk_term(bitwuzla.Kind.BV_AND, [not_bit4, not_bit5])

    s0_0_s1_3 = bitwuzla.mk_term(bitwuzla.Kind.BV_AND, [s0_0, s1_3])
    s0_3_s1_0 = bitwuzla.mk_term(bitwuzla.Kind.BV_AND, [s1_0, s0_3])
    s1_0_s2_3 = bitwuzla.mk_term(bitwuzla.Kind.BV_AND, [s1_0, s2_3])
    s1_3_s2_0 = bitwuzla.mk_term(bitwuzla.Kind.BV_AND, [s2_0, s1_3])
    s2_0_s3_3 = bitwuzla.mk_term(bitwuzla.Kind.BV_AND, [s2_0, s3_3])
    #s2_3_s3_0 = bitwuzla.mk_term(bitwuzla.Kind.BV_AND, [s3_0, s2_3])

    s3_n0 = bitwuzla.mk_term(bitwuzla.Kind.BV_OR, [not_bit7, not_bit6])    
    
    # Create the inequality comparison
    mta_equality_term0 = bitwuzla.mk_term(bitwuzla.Kind.EQUAL, [s0_0_s1_3, zero_val])
    mta_equality_term1 = bitwuzla.mk_term(bitwuzla.Kind.EQUAL, [s0_3_s1_0, zero_val])
    mta_equality_term2 = bitwuzla.mk_term(bitwuzla.Kind.EQUAL, [s1_0_s2_3, zero_val])
    mta_equality_term3 = bitwuzla.mk_term(bitwuzla.Kind.EQUAL, [s1_3_s2_0, zero_val])
    mta_equality_term4 = bitwuzla.mk_term(bitwuzla.Kind.EQUAL, [s2_0_s3_3, zero_val])
    #mta_equality_term5 = bitwuzla.mk_term(bitwuzla.Kind.EQUAL, [s2_3_s3_0, zero_val])

    mta_or_term = bitwuzla.mk_term(bitwuzla.Kind.EQUAL, [s3_n0, one_val])
  
    
    # Assert the constraint
    bitwuzla_solver.assert_formula(mta_equality_term0)
    bitwuzla_solver.assert_formula(mta_equality_term1)
    bitwuzla_solver.assert_formula(mta_equality_term2)
    bitwuzla_solver.assert_formula(mta_equality_term3)
    bitwuzla_solver.assert_formula(mta_equality_term4)
    #bitwuzla_solver.assert_formula(mta_equality_term5)
    bitwuzla_solver.assert_formula(mta_or_term)
    
    

    
    #check pair wise equality
    for j in range(lcv+1,len(code)):
        not_equal_term = bitwuzla.mk_term(
            bitwuzla.Kind.DISTINCT, 
            [code[lcv], code[j]]
        )
        bitwuzla_solver.assert_formula(not_equal_term)


# force seed to use position 1
#seeded_term = bitwuzla.mk_term(bitwuzla.Kind.BV_EXTRACT, [enc_position_bvs[0]], [0,0])
#bitwuzla_solver.assert_formula(bitwuzla.mk_term(bitwuzla.Kind.EQUAL,[seeded_term, zero_val]))

for j in range(ENC_GATES):
    if(j < BITSi):
        seeded_term = bitwuzla.mk_term(bitwuzla.Kind.BV_EXTRACT, [enc_dc_bvs[j]], [j,j])
        bitwuzla_solver.assert_formula(bitwuzla.mk_term(bitwuzla.Kind.EQUAL,[seeded_term, zero_val]))

#for i in range(BITSi):
#    seeded_term = bitwuzla.mk_term(bitwuzla.Kind.BV_EXTRACT, [enc_dc_bvs[0]], [i,i])
#    bitwuzla_solver.assert_formula(bitwuzla.mk_term(bitwuzla.Kind.EQUAL,[seeded_term, one_val]))

#extracted_enable = bitwuzla.mk_term(bitwuzla.Kind.BV_EXTRACT, [enc_gate_enable[0]],[0,0]) 
#bitwuzla_solver.assert_formula(bitwuzla.mk_term(bitwuzla.Kind.EQUAL,[extracted_enable,one_val]))


#for i in range(BITSo):
#    seeded_term = bitwuzla.mk_term(bitwuzla.Kind.BV_EXTRACT, [code[0]], [i,i])
#    bitwuzla_solver.assert_formula(bitwuzla.mk_term(bitwuzla.Kind.EQUAL,[seeded_term, zero_val]))

 
start_time = time.time()
result = bitwuzla_solver.check_sat()
end_time = time.time()
print(f'Bitwuzla: {result}' + ' and time =  ' + str(end_time-start_time),flush=True)

if(result != 'unsat'):
    for lcv in range(ROWS):
        temp = str(bitwuzla_solver.get_value(code[lcv]))
        print('lcv = ' + str(lcv) + ' code = ' + str(temp) + ' value ' + str(int(temp[2:],2)))
    print('Encoder ')
    for j in range(ENC_GATES):
        minterm_str = str(bitwuzla_solver.get_value(enc_position_bvs[j]))
        minterm_str = minterm_str[2:]
        dc_str = str(bitwuzla_solver.get_value(enc_dc_bvs[j]))
        dc_str = dc_str[2:]
        output_str = ""
        for i in range(BITSi):
            if(dc_str[i] == "1"):
                output_str += "-"
            else:
                output_str += minterm_str[i]

        print('encoder minterm is ' + output_str)
    

    print('Enc Enables')
    for j in range(BITSo):
        temp = str(bitwuzla_solver.get_value(enc_gate_enable[j]))
        print('enc pin = ' + str(j) + ' code = ' + str(temp))
 
    print('Enc DC')
    for j in range(ENC_GATES):
        temp = str(bitwuzla_solver.get_value(enc_dc_bvs[j]))
        print('enc pin = ' + str(j) + ' code = ' + str(temp))


    print('Decoder ')
    for j in range(DEC_GATES):
        minterm_str = str(bitwuzla_solver.get_value(dec_position_bvs[j]))
        minterm_str = minterm_str[2:]
        dc_str = str(bitwuzla_solver.get_value(dec_dc_bvs[j]))
        dc_str = dc_str[2:]
        output_str = ""
        for i in range(BITSo):
            if(dc_str[i] == "1"):
                output_str += "-"
            else:
                output_str += minterm_str[i]

        print('decoder minterm is ' + output_str)
    
    print('Dec Enables')
    for j in range(BITSi):
        temp = str(bitwuzla_solver.get_value(dec_gate_enable[j]))
        print('dec pin = ' + str(j) + ' code = ' + str(temp))
