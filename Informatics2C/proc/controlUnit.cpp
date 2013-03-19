// Inf2C Computer Systems, Processor design practical
// Copyright 2004-2011, School of Informatics, The University of Edinburgh

// Control unit for processor. 

// Template file. 
// Only contains implementation for j, addi and halt instructions.

#include "systemc.h"
#include "controlUnit.h"
#include "defines.h"

void controlUnit::ctrl_regs()
{
    sc_uint<3> t_next_cycle;

    while (1) {
        wait(); // wait for reset or clock

        if (reset) {
            wait(1, SC_NS);
            cur_cycle = 0;
            cycle_count = 0;
        } else {
            if (halt.read()) {
                // endSimulation
                std::cout << sc_time_stamp()
                          <<" Halting simulation!"
                          << std::endl
                          << "Cycles = "
                          << cycle_count
                          << std::endl;
                sc_stop();
                // No return instruction needed.
            }
            cycle_count++;
            t_next_cycle = next_cycle;
            wait(1, SC_NS);
            cur_cycle = t_next_cycle;
        }
    }
}



void controlUnit::ctrl_comb()
{
    sc_int<32> t_ir = ir;

    // Extract useful subfields of the instruction
    opcode = t_ir.range(31,26);
    subfunct = t_ir.range(5,0);

    // Default values for various control fields

    halt = false;
    mem_rd = false;
    mem_wrt = false;

    ldPC = false; 
    ldIR = false; 
    ldReg = false;

    ldMAR = false;
    ldALUout = false;
    ldMDLR = false;
    ldMDSR = false;

    // Defaults for multiplexer settings and ALU function.
    // While defaults are set here, the main code should always set these
    // explicitly to make intent clear.

    wreg_addr_mux = WA_RD;  
    pc_mux = PC_ALU; 
    addr_mux = ADDR_PC;  
    a_mux = A_PC;
    b_mux = B_REG;
    reg_write_mux = RW_ALU_OUT; 
    func = ADD;

    switch(cur_cycle.read()){

    case(0): // Cycle 0
        // Instruction fetch.  Same for all instructions
        next_cycle = 1; 
        mem_rd = true;
        ldPC = true;
        ldIR = true;
        pc_mux=PC_ALU;
        addr_mux = ADDR_PC;
        a_mux = A_PC;
        b_mux = B_4;
        func = ADD;
        break;
    case(1): // Cycle 1
        if (opcode == 0x0 && subfunct == 0xc) {
            // halt instruction
            printf("Halt instruction\n");
            halt = true;
        }
        else if (opcode == 0x2) {
            // jump instruction
            next_cycle = 0;  
            ldPC = true;  
            pc_mux = PC_IMM;
        }

        else if (opcode == 0x8) {
            // addi instruction
            next_cycle = 2;
            ldALUout = true;
            a_mux = A_REG;
            b_mux = B_IR_16;
            func = ADD;
        }
		else if (opcode == 0x0 && subfunct == 0x20) {
			//add instruction
			next_cycle = 2;
			ldALUout = true;
			a_mux = A_REG;
			b_mux = B_REG;
			func = ADD;
		}
		else if (opcode == 0x0 && subfunct == 0x22) {
			//sub instruction
			next_cycle = 2;
			ldALUout = true;
			a_mux = A_REG;
			b_mux = B_REG;
			func = SUB;
		}
		else if (opcode == 0x2b) {
			//sw instruction
			next_cycle=2;
			ldMAR = true;
			ldMDSR = true;
			a_mux = A_REG;
			b_mux = B_IR_16;
			func = ADD;
		}
		else if (opcode == 0x23) {
			//lw instruction
			ldMAR = true;
			a_mux = A_REG;
			b_mux = B_IR_16;
			func = ADD;
		}
		else if (opcode == 0x4) {
			//beq instruction
			next_cycle = 2;
			a_mux = A_REG;
			b_mux = B_REG;
			func = SUB;
		}
		else if (opcode == 0x5) {
			//bne instruction
			next_cycle = 2;
			a_mux = A_REG;
			b_mux = B_REG;
			func = SUB;
		}
        else {
            // unrecognised instruction
            std::cout << "At " << sc_time_stamp() << ": ";
            printf("unrecognized instruction (opcode=0x%x, subfunct=0x%x)",
                   opcode,
                   subfunct);
            std::cout << ", cycle 1" << std::endl;
            halt = true;
        }
        break;
    case (2): // Cycle 2
        if (opcode == 0x8  ) { // addi 

            next_cycle = 0;
            ldReg = true;
            wreg_addr_mux = WA_RT;
            reg_write_mux = RW_ALU_OUT;
            
        }
		else if (opcode == 0x0 && subfunct == 0x20) { //add
			next_cycle = 0;
			ldReg = true;
			wreg_addr_mux = WA_RD;
			reg_write_mux = RW_ALU_OUT;

		}
		else if (opcode == 0x0 && subfunct == 0x22) { //sub
			next_cycle = 0;
			ldReg = true;
			wreg_addr_mux = WA_RD;
			reg_write_mux = RW_ALU_OUT;
		}

		else if (opcode == 0x2b) { //sw
			next_cycle = 0;
			mem_wrt = true;
			addr_mux = ADDR_MAR;
		}
		else if (opcode == 0x23) { //lw
			next_cycle = 3;
			mem_rd = true;
			ldMDLR = true;
			addr_mux = ADDR_MAR;
		}
		else if (opcode == 0x4 && zero == true) { // beq when equal
			next_cycle = 0;
			ldPC = true;
			pc_mux = PC_ALU;
			a_mux = A_PC;
			b_mux = B_IR_16X4;
			func = ADD;
		}
		else if (opcode == 0x4 && zero == false) { //beq when not equal
			next_cycle = 0;
		}
		else if (opcode == 0x4 && zero == false) { //bne when not equal
			next_cycle = 0;
			ldPC = true;
			pc_mux = PC_ALU;
			a_mux = A_PC;
			b_mux = B_IR_16X4;
			func = ADD;
		}
		else if (opcode == 0x4 && zero == true) { //bne when equal
			next_cycle = 0;
		}
        else {
            // unrecognised instruction
            std::cout << "At " << sc_time_stamp() << ": ";
            printf("unrecognized instruction (opcode=0x%x, subfunct=0x%x)",
                opcode,
                subfunct);
            std::cout << ", cycle 2" << std::endl;
            halt = true;
        }
        break;
    case (3): // Cycle 3
		if (opcode == 0x23) { // lw
			next_cycle = 0;
		    ldReg = true;
			wreg_addr_mux = WA_RT;
			reg_write_mux = RW_MEM;
		}
        else {
            // unrecognised instruction
            std::cout << "At " << sc_time_stamp() << ": ";
            printf("unrecognized instruction (opcode=0x%x, subfunct=0x%x)",
                opcode,
                subfunct);
            std::cout << ", cycle 3" << std::endl;
            halt = true;
        }
        break;
    default: // Cycle 4+
        std::cout << "At " << sc_time_stamp() << ": ";
        std::cout << "unexpected current state " << cur_cycle.read();
        std::cout << std::endl;
        halt = true;

    } // end switch(cur_state)

    return;
}
