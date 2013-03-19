#  Question from cw1 - counting how many time every character occurs in a string
#  Written by Stefan Sabev
        
        .data
prompt1:                                    .asciiz  "Enter a string followed by $:\n"
nl:                                         .asciiz  "\n"
cl:                                         .asciiz  ": "
letters:                                    .word 0:26

        .globl main

        .text
main:   
        li $v0, 4                           # prompt for input
        la $a0, prompt1
        syscall
        
        add $t0, $zero, $zero               # make sure $t0 is empty
        
loop:
        add $t5, $zero, $zero               # make sure this is zero as it will be used

        li $v0, 12                          # read characters
        syscall
        
        beq $v0, 36, print                  # if the character is $ ust jump to the end of the program
 
        beq $v0, 0x20, loop                 # if space, ignore charter jump to loop
        beq $v0, 0x09, loop                 # if tab, do the same as for space
        beq $v0, 0x0a, loop                 # if newlined, do the same as for space
        beq $v0, 0x0d, loop                 # if carriage-return do the same as for the space
        

        bge $v0, 97, lowercases             # if the character is lowercase jump to lowercases for some additional processing
        ble $v0, 90, array_handling         # if character is a capital letter
        
        # jump back to the loop
        j loop

lowercases:                                 # helper function which just substracts 32 from the ascii
        sub $v0, $v0, 32                    # value of the character to convert to uppercase

        j array_handling                    # go to array_handling

array_handling:                             # the counting of letters is done in here

        sub $t0, $v0, 65                    # substract 65 from the character so it's in the range 0:26, so this will the index
        la $t3, letters                     # put address of list into $t3
        add $t2, $t0, 0                     # put the index into $t2
        add $t2, $t2, $t2                   # double the index
        add $t2, $t2, $t2                   # double the index again (now 4x)
        add $t1, $t2, $t3                   # combine the two components of the address
        lw $t4, 0($t1)                      # load the value into $t4 from the array cell
        add $t4, $t4, 1                     # increment $t4 by one
        sw $t4, 0($t1)                      # store the value of $t4 into the array cell
        
        j loop                              # when array_handling is done for the character jump back to the main loop

print:
                                            # this is is the loop that handles the printing
                                            # $t5 will start from zero and the increment up to 26
        beq $t5, 26, end                    # if the value of $t5 is 26 jump to the end
        
        li $v0, 4                           
        la $a0, nl
        syscall                             # print out a newline
x
        add $t6, $t5, 65                    # load the value of $t5 which is the loop counter and add 65 to it
                                            # then assign that to $t6 so we can print out ASCII uppercase letters

        li $v0, 11                          # print current character
        ori $a0, $t6,0
        syscall

        li $v0, 4
        la $a0, cl                          # then a colon and a space
        syscall
        
        la $t3, letters                     # put address of list into $t3
        add $t2, $t5, 0                     # put the index which is going to be $t5 ranging from 0 to 26 ( for all the letters )
        add $t2, $t2, $t2                   # double the index
        add $t2, $t2, $t2                   # double the index again
        add $t1, $t2, $t3                   # combine the two components of the address
        lw $t4, 0($t1)                      # load of the value of letter[$t5] into $t4

        
        li $v0, 1                           # print out the number of occurences of the $t5-th letter in the alphabet
        ori $a0, $t4, 0
        syscall
        
        add $t5, $t5, 1                     # add 1 to $t5 and jump back to print

        j print
end:
        li $v0, 10                          # end the program
        syscall

