// Constants for multiplexer controls

// wreg_addr_mux 
#define WA_RD  0
#define WA_RT  1
#define WA_31  2

// pc_mux
#define PC_ALU  false
#define PC_IMM  true

// addr_mux
#define ADDR_PC  false
#define ADDR_MAR true

// a_mux
#define A_REG false
#define A_PC  true

// b_mux
#define B_REG      0
#define B_4        1
#define B_0        2
#define B_IR_16    3
#define B_IR_16X4  4

// reg_write_mux
#define RW_ALU_OUT false
#define RW_MEM    true

// func
#define ADD  0
#define SUB  1
#define AND  2
#define OR   3
#define EOR  4

#
