# Question from cw1 - counting chars in a string
# Written by Stefan Sabev
        
        .data
prompt1:        .asciiz  "Enter a string followed by $:\n"
outmsg:         .asciiz  "\nCount:"

        .globl main

        .text
main:   
        li $v0, 4                           # prompt for input
        la $a0, prompt1
        syscall
        
        add $t0, $zero, $zero               # make sure $t0 is empty
        
loop:
        li $v0, 12                          # read characters
        syscall
        
        beq $v0, 36, print                  # if the character is $ ust jump to the end of the program
 
        beq $v0, 0x20, loop                 # if space, ignore charter jump to loop
        beq $v0, 0x09, loop                 # if tab, do the same as for space
        beq $v0, 0x0a, loop                 # if newlined, do the same as for space
        beq $v0, 0x0d, loop                 # if carriage-return do the same as for the space

        add   $t0, $t0, 1                   # Add 1 to $t0 for every execution of the loop when not branched.


        j loop                              # Jump back to the loop

print:
        li $v0, 4                           # Print the "Count:" message
        la $a0, outmsg 
        syscall

        li $v0, 1
        add $a0, $t0, $zero                 # Print out the actual count which is stored in $t0
        syscall

        li $v0, 10                          # Close the program
        syscall

