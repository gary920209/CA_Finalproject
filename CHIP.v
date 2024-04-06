//----------------------------- DO NOT MODIFY THE I/O INTERFACE!! ------------------------------//
module CHIP #(                                                                                  //
    parameter BIT_W = 32                                                                        //
)(                                                                                              //
    // clock                                                                                    //
        input               i_clk,                                                              //
        input               i_rst_n,                                                            //
    // instruction memory                                                                       //
        input  [BIT_W-1:0]  i_IMEM_data,                                                        //
        output [BIT_W-1:0]  o_IMEM_addr,                                                        //
        output              o_IMEM_cen,                                                         //
    // data memory                                                                              //
        input               i_DMEM_stall,                                                       //
        input  [BIT_W-1:0]  i_DMEM_rdata,                                                       //
        output              o_DMEM_cen,                                                         //
        output              o_DMEM_wen,                                                         //
        output [BIT_W-1:0]  o_DMEM_addr,                                                        //
        output [BIT_W-1:0]  o_DMEM_wdata,                                                       //
    // finnish procedure                                                                        //
        output              o_finish,                                                           //
    // cache                                                                                    //
        input               i_cache_finish,                                                     //
        output              o_proc_finish                                                       //
);                                                                                              //
//----------------------------- DO NOT MODIFY THE I/O INTERFACE!! ------------------------------//

// ------------------------------------------------------------------------------------------------------------------------------------------------------
// Parameters
// ------------------------------------------------------------------------------------------------------------------------------------------------------
    // TODO: any declaration
    // ========  FSM  ==========
    // FSM based on operation cycles
    parameter S_INIT           = 2'd0;
    parameter S_MEM_ACCESS     = 2'd1;
    parameter S_MUL            = 2'd2;
    parameter S_TERMINAL       = 2'd3;

// ------------------------------------------------------------------------------------------------------------------------------------------------------
// Wires and Registers
// ------------------------------------------------------------------------------------------------------------------------------------------------------
    
    // TODO: any declaration
        reg  [BIT_W-1:0] PC, next_PC;
        reg mem_cen, mem_wen;
        reg [BIT_W-1:0] mem_addr, mem_wdata;
        //reg [BIT_W-1:0] mem_rdata;
        //reg mem_stall;
        reg  [     1: 0] state, state_nxt; 
        wire [    31: 0] instruction;
        reg  [    31: 0] reg_wdata;
        reg              reg_wen;
        wire [    31: 0] reg_rdata1, reg_rdata2;
        reg  [    31: 0] result;
        wire  mul_valid;
        wire  [    31: 0] mul_result,mul_result_overflow;
        wire  mul_done;
// ------------------------------------------------------------------------------------------------------------------------------------------------------
// Continuous Assignment
// ------------------------------------------------------------------------------------------------------------------------------------------------------

    // TODO: any wire assignment
    assign o_IMEM_addr = PC;
    assign o_IMEM_cen  = (state != S_TERMINAL) ? 1'b1 : 1'b0;

    assign instruction = i_IMEM_data;
    assign o_proc_finish  = (state_nxt == S_TERMINAL) ? 1'b1 : 1'b0;
    assign o_finish = i_cache_finish;
    assign o_DMEM_cen = mem_cen;
    assign o_DMEM_wen = mem_wen;
    assign o_DMEM_addr = mem_addr;
    assign o_DMEM_wdata = mem_wdata;
    // assign i_DMEM_rdata = mem_rdata;
    // assign i_DMEM_stall = mem_stall;
    assign mul_valid = (state == S_INIT && state_nxt == S_MUL && i_rst_n) ? 1'b1 : 1'b0;

// ------------------------------------------------------------------------------------------------------------------------------------------------------
// Submoddules
// ------------------------------------------------------------------------------------------------------------------------------------------------------

    // TODO: Reg_file wire connection
    Reg_file reg0(               
        .i_clk  (i_clk),             
        .i_rst_n(i_rst_n),         
        .wen    (reg_wen),          
        .rs1    (instruction[19:15]),                
        .rs2    (instruction[24:20]),                
        .rd     (instruction[11:7]),                 
        .wdata  (reg_wdata),             
        .rdata1 (reg_rdata1),           
        .rdata2 (reg_rdata2)
    );
    MULDIV_unit M1(
        .i_clk  (i_clk),             
        .i_rst_n(i_rst_n),         
        .i_valid(mul_valid),             
        .i_A    (reg_rdata1),           
        .i_B    (reg_rdata2),           
        .i_inst (3'd6),    
        .o_data ({mul_result_overflow,mul_result}),           
        .o_done (mul_done)
    );
    
// ------------------------------------------------------------------------------------------------------------------------------------------------------
// Always Blocks
// ------------------------------------------------------------------------------------------------------------------------------------------------------
    //ALU
    always @(*) begin
        if(instruction[6:0] == 7'b0110011)begin
            case(instruction[14:12])
                3'b000:begin
                    if(instruction[30] == 1'b1)
                        result = reg_rdata1 - reg_rdata2;
                    else
                        result = reg_rdata1 + reg_rdata2;
                end
                3'b100: result = reg_rdata1 ^ reg_rdata2;
                3'b111: result = reg_rdata1 & reg_rdata2;
                default: result = 32'h0;
            endcase
        end
        else if(instruction[6:0] == 7'b0010011)begin
            case(instruction[14:12])
                3'b000: result = reg_rdata1 + {{20{instruction[31]}},instruction[31:20]};
                3'b001: result = reg_rdata1 << {{27{instruction[24]}},instruction[24:20]};
                3'b010: result = ( ((reg_rdata1[31] == 1'b1) && (instruction[31] == 1'b0))
                    || ((reg_rdata1[31] == instruction[31]) && (reg_rdata1 < {{20{instruction[31]}},instruction[31:20]}))
                    ) ? 32'b1 : 32'b0;
                //dangerous
                3'b101: result = reg_rdata1 >>> {{27{instruction[24]}},instruction[24:20]};
                default: result = 32'h0;
            endcase
        end
        else
            result = 32'h0;
    end
    //pcnxt function
    always @(*) begin
        if(instruction[6:0] == 7'b1101111) begin
            next_PC = PC + {{12{instruction[31]}}, instruction[19:12], instruction[20], instruction[30:21], 1'b0};
        end
        else if(instruction[6:0] == 7'b1100111) begin
            next_PC = {{20{instruction[31]}},instruction[31:20]} + reg_rdata1;
        end
        else if(instruction[6:0] == 7'b1100011) begin
            case(instruction[14:12])
                3'b000: begin
                    if(reg_rdata1 == reg_rdata2)
                        next_PC = PC + {{12{instruction[31]}}, instruction[7], instruction[30:25], instruction[11:8], 1'b0};
                    else
                        next_PC = PC + 32'h4;
                end
                3'b001: begin
                    if(reg_rdata1 != reg_rdata2)
                        next_PC = PC + {{12{instruction[31]}}, instruction[7], instruction[30:25], instruction[11:8], 1'b0};
                    else
                        next_PC = PC + 32'h4;
                end
                3'b100: begin
                    if( ((reg_rdata1[31] == 1'b1) && (reg_rdata2[31] == 1'b0)) 
                        || ((reg_rdata1[31] == reg_rdata2[31]) && (reg_rdata1 < reg_rdata2))
                    )
                        next_PC = PC + {{12{instruction[31]}}, instruction[7], instruction[30:25], instruction[11:8], 1'b0};
                    else
                        next_PC = PC + 32'h4;
                end
                3'b101: begin
                    if( ((reg_rdata1[31] == 1'b1) && (reg_rdata2[31] == 1'b0)) 
                        || ((reg_rdata1[31] == reg_rdata2[31]) && (reg_rdata1 < reg_rdata2))
                    )
                        next_PC = PC + 32'h4;
                    else
                        next_PC = PC + {{12{instruction[31]}}, instruction[7], instruction[30:25], instruction[11:8], 1'b0};
                end
                default: begin
                    next_PC = PC + 32'h4;
                end
            endcase
        end
        else if (state_nxt != S_INIT)begin
            next_PC = PC;
        end
        else begin
            next_PC = PC + 32'h4;
        end

    end

    //mem access
    always @(*) begin
        if(!i_rst_n ) begin
            mem_cen = 1'b0;
            mem_wen = 1'b0;
            mem_addr = 32'h0;
            mem_wdata = 32'h0;
        end
        else if (instruction[6:0] == 7'b0000011 && state == S_INIT) begin
            mem_cen = 1'b1;
            mem_wen = 1'b0;
            mem_addr = reg_rdata1 + {{20{instruction[31]}},instruction[31:20]};
            mem_wdata = 32'b0;
        end
        else if (instruction[6:0] == 7'b0100011 && state == S_INIT)begin
            mem_cen = 1'b1;
            mem_wen = 1'b1;
            mem_addr = reg_rdata1 + {{20{instruction[31]}},instruction[31:25], instruction[11:7]};
            mem_wdata = reg_rdata2;
        end
        else begin
            mem_cen = 1'b0;
            mem_wen = 1'b0;
            mem_addr = 32'h0;
            mem_wdata = 32'h0;
        end
    end
    //reg write
    always @(*) begin
        if (i_clk == 1'b0 && instruction[11:7]!= 5'b00000 && state_nxt != S_TERMINAL && i_rst_n) begin
            if(instruction[6:0] == 7'b0110011 && instruction[25] == 1'b0) begin
                reg_wdata = result;
                reg_wen = 1'b1;
            end
            else if(instruction[6:0] == 7'b0010011) begin
                reg_wdata = result;
                reg_wen = 1'b1;
            end 
            else if(instruction[6:0] == 7'b0010111) begin
                reg_wdata = PC + {instruction[31:12],12'b0};
                reg_wen = 1'b1;
            end
            else if(instruction[6:0] == 7'b1101111 || instruction[6:0] == 7'b1100111) begin
                reg_wdata = PC + 32'b100;
                reg_wen = 1'b1;
            end
            else if(instruction[6:0] == 7'b0000011 && state == S_MEM_ACCESS && i_DMEM_stall == 0) begin
                reg_wdata = i_DMEM_rdata;
                reg_wen = 1'b1;
            end
            else if(state == S_MUL && mul_done == 1'b1) begin
                reg_wdata = mul_result;
                reg_wen = 1'b1;
            end
            else begin
                reg_wen = 1'b0;                 
                reg_wdata = result;            
            end
        end
        else begin
            reg_wen = 1'b0;                 
            reg_wdata = result;
        end
    end

    // Todo: FSM
    always @(*) begin
        case(state)
            S_INIT: begin
                if (instruction[6:0] == 7'b0000011 || instruction[6:0] == 7'b0100011)
                    state_nxt = S_MEM_ACCESS;
                else if (instruction[6:0] == 7'b0110011 && instruction[25] == 1'b1)
                    state_nxt = S_MUL;
                else if (instruction == 32'h00000073)
                    state_nxt = S_TERMINAL;
                else
                    state_nxt = S_INIT;
            end
            S_MEM_ACCESS: begin
                if (i_DMEM_stall == 0)
                    state_nxt = S_INIT;
                else
                    state_nxt = S_MEM_ACCESS;
            end
            S_MUL: begin
                if (mul_done == 1'b1)
                    state_nxt = S_INIT;
                else
                    state_nxt = S_MUL;
            end
            S_TERMINAL: begin
                state_nxt = S_TERMINAL;
            end
            default: begin
                state_nxt = state;
            end
        endcase
    end


    always @(posedge i_clk or negedge i_rst_n) begin
        if (!i_rst_n) begin
            PC <= 32'h00010000; // Do not modify this value!!!
            state <= S_INIT;
        end
        else begin
            PC <= next_PC;
            state <= state_nxt;
        end
    end
endmodule

module Reg_file(i_clk, i_rst_n, wen, rs1, rs2, rd, wdata, rdata1, rdata2);
   
    parameter BITS = 32;
    parameter word_depth = 32;
    parameter addr_width = 5; // 2^addr_width >= word_depth
    
    input i_clk, i_rst_n, wen; // wen: 0:read | 1:write
    input [BITS-1:0] wdata;
    input [addr_width-1:0] rs1, rs2, rd;

    output [BITS-1:0] rdata1, rdata2;

    reg [BITS-1:0] mem [0:word_depth-1];
    reg [BITS-1:0] mem_nxt [0:word_depth-1];

    integer i;

    assign rdata1 = mem[rs1];
    assign rdata2 = mem[rs2];

    always @(*) begin
        for (i=0; i<word_depth; i=i+1)
            mem_nxt[i] = (wen && (rd == i)) ? wdata : mem[i];
    end

    always @(posedge i_clk or negedge i_rst_n) begin
        if (!i_rst_n) begin
            mem[0] <= 0;
            for (i=1; i<word_depth; i=i+1) begin
                case(i)
                    32'd2: mem[i] <= 32'hbffffff0;
                    32'd3: mem[i] <= 32'h10008000;
                    default: mem[i] <= 32'h0;
                endcase
            end
        end
        else begin
            mem[0] <= 0;
            for (i=1; i<word_depth; i=i+1)
                mem[i] <= mem_nxt[i];
        end       
    end
endmodule

module MULDIV_unit#(
    parameter DATA_W = 32
    // TODO: port declaration
    )(
    input                       i_clk,   // clock
    input                       i_rst_n, // reset

    input                       i_valid, // input valid signal
    input [DATA_W - 1 : 0]      i_A,     // input operand A
    input [DATA_W - 1 : 0]      i_B,     // input operand B
    input [         2 : 0]      i_inst,  // instruction

    output [2*DATA_W - 1 : 0]   o_data,  // output value
    output                      o_done   // output valid signal
    );
// Parameters
    // ======== choose your FSM style ==========
    // 1. FSM based on operation cycles
    parameter S_IDLE           = 2'd0;
    parameter S_ONE_CYCLE_OP   = 2'd1;
    parameter S_MULTI_CYCLE_OP = 2'd2;

// Wires & Regs
    // Todo
    // state
    reg  [         1: 0] state, state_nxt; // remember to expand the bit width if you want to add more states!

    // load input
    reg  [  DATA_W-1: 0] operand_a, operand_a_nxt;
    reg  [  DATA_W-1: 0] operand_b, operand_b_nxt;
    reg  [         2: 0] inst, inst_nxt;
    //other
    reg  [2*DATA_W-1: 0] output_data;
    reg  [2*DATA_W-1: 0] output_nxt;
    reg  [         4: 0] mul_div_counter;
    reg  [         4: 0] counter_nxt;
    reg  oDone;
    reg  oDone_nxt;
    reg  [2*DATA_W-1: 0] temp1, temp2;
// Wire Assignments
    // Todo
    assign o_done = oDone;
    assign o_data = output_data;
  
// Always Combination
    // load input
    always @(*) begin
        if (i_valid) begin
            operand_a_nxt = i_A;
            operand_b_nxt = i_B;
            inst_nxt      = i_inst;
        end
        else begin
            operand_a_nxt = operand_a;
            operand_b_nxt = operand_b;
            inst_nxt      = inst;
        end
    end
    // Todo: FSM
    always @(*) begin
        case(state)
            S_IDLE           : // if i_inst = 0~5, we can go s_one_cycle_op
            if (i_valid) begin
                if (i_inst >= 3'd6)
                    state_nxt = S_MULTI_CYCLE_OP;
                else
                    state_nxt = S_ONE_CYCLE_OP;
            end else 
                state_nxt = S_IDLE;

            S_ONE_CYCLE_OP   :
                state_nxt = S_IDLE;
            
            // if(i_inst == 3d'0)
            //     state_nxt = S_ADD;
            // else if(i_inst == 3d'1)
            //     state_nxt = S_SUB;
            // else if(i_inst == 3d'2)
            //     state_nxt = S_AND;
            // else if(i_inst == 3d'3)
            //     state_nxt = S_OR;
            // else if(i_inst == 3d'4)
            //     state_nxt = S_SLT;
            // else 
            //     state_nxt = S_SRA;

            S_MULTI_CYCLE_OP :

            if (mul_div_counter == 31) 
                // Transition o the next state after 32 cycles
                state_nxt = S_IDLE;
            else 
                // Stay in the S_MULTI_CYCLE_OP state until 32 cycles are completed
                state_nxt = S_MULTI_CYCLE_OP;
            
            default : state_nxt = state;
        endcase
    end
    // Todo: Counter
    // Counter for MUL/DIV cycles
    always @(*) begin
		if (state == S_MULTI_CYCLE_OP) 
				counter_nxt = mul_div_counter + 1;
		else 
				counter_nxt = 0;
	end

    // Todo: ALU output
    always @(*) begin
        output_nxt[2*DATA_W-1:0] = 0;
        case (state)
            S_ONE_CYCLE_OP : begin
                case (inst)
                    3'b000: begin 
                        output_nxt[DATA_W-1:0] = operand_a[DATA_W-1:0]+ operand_b[DATA_W-1:0]; // ADD
                        //check overflow
                        if (operand_a[DATA_W-1] == 1'b0 && operand_b[DATA_W-1] == 1'b0 && output_nxt[DATA_W-1] == 1'b1)
                            output_nxt = 32'h7fffffff;
                        else if(operand_a[DATA_W-1] == 1'b1 && operand_b[DATA_W-1] == 1'b1 && output_nxt[DATA_W-1] == 1'b0)
                            output_nxt = 32'h80000000;
                    end

                    3'b001: begin 
                        output_nxt[DATA_W-1:0] = operand_a[DATA_W-1:0] - operand_b[DATA_W-1:0]; // SUB
                        //check overflow
                        if (operand_a[DATA_W-1] != operand_b[DATA_W-1] && output_nxt[DATA_W-1] != operand_a[DATA_W-1]) begin
                            if(operand_a[DATA_W-1] == 1) begin
                                output_nxt = 32'h80000000; 
                            end
                            else begin
                                output_nxt = 32'h7fffffff; 
                            end
                        end  
                    end

                    3'b010: output_nxt[DATA_W-1:0] = operand_a[DATA_W-1:0] & operand_b[DATA_W-1:0]; // AND
                    3'b011: output_nxt[DATA_W-1:0] = operand_a[DATA_W-1:0] | operand_b[DATA_W-1:0]; // OR
                    3'b100: begin
					if(operand_a[DATA_W-1] == 1'b1 && operand_b[DATA_W-1] == 1'b0)
						output_nxt = 1;
					else if(operand_a[DATA_W-1] == 1'b0 && operand_b[DATA_W-1] == 1'b1)
						output_nxt = 0;
					else
						output_nxt =  (operand_a[DATA_W-1:0] < operand_b[DATA_W-1:0]) ? 1 : 0;
					end
					
					// output_data[DATA_W-1:0] = (operand_a[DATA_W-1:0] < operand_b[DATA_W-1:0]) ? 1 : 0; // SLT
					3'b101: output_nxt[DATA_W-1:0] = $signed(operand_a[DATA_W-1:0]) >>> operand_b[DATA_W-1:0]; // SRA
                    
                    default: output_nxt = 0;
                endcase
            end


            S_MULTI_CYCLE_OP:begin
                temp1[2*DATA_W-1:0] = 0;
                temp2[2*DATA_W-1:0] = 0;
                case(inst)
                    3'b110: begin
                        // temp2 store the temp output
                        if (mul_div_counter == 0) begin
							temp2[2*DATA_W-1:0] = operand_b >> 1;
                            if(operand_b[0] == 1'b1) begin
                                temp1[2*DATA_W-1:0] = operand_a << DATA_W-1;
                                temp2[2*DATA_W-1:0] = temp1[2*DATA_W-1:0] + temp2[2*DATA_W-1:0];
                            end
                        end
                        else if (mul_div_counter < 32) begin
                            temp2[2*DATA_W-1:0] = output_data[2*DATA_W-1:0] >> 1;
                            if(output_data[0] == 1'b1) begin
                                temp1[2*DATA_W-1:0] = operand_a << DATA_W-1;
                                temp2[2*DATA_W-1:0] = temp1[2*DATA_W-1:0] + temp2[2*DATA_W-1:0];
                            end
                             // MUL
                             // b = b + a
    
                        end
                        else begin
                            output_nxt = 0;
                        end
                        output_nxt[2*DATA_W-1:0] = temp2[2*DATA_W-1:0];
                    end
                    3'b111: begin
                        if(mul_div_counter == 0)    
                            temp2[2*DATA_W-1:0] = operand_a << 1;       
                        else 
                            temp2[2*DATA_W-1:0] = output_data[2*DATA_W-1:0];               

                        if (mul_div_counter < 31) begin
                            temp1[DATA_W-1:0] = temp2[2*DATA_W-1:DATA_W];     
                            if (temp1[DATA_W-1:0] >= operand_b) begin
                                temp1[DATA_W-1:0] = temp1[DATA_W-1:0] - operand_b[DATA_W-1:0];
                                temp2[2*DATA_W-1:DATA_W] = temp1[DATA_W-1:0];
                                temp2[2*DATA_W-1:0] = temp2[2*DATA_W-1:0] << 1;
                                temp2[2*DATA_W-1:0] = temp2[2*DATA_W-1:0] + 1'b1;
                            end
                            else begin
                                temp2[2*DATA_W-1:0] = temp2[2*DATA_W-1:0] << 1;
                            end
                            output_nxt[2*DATA_W-1:0] = temp2[2*DATA_W-1:0];
                            //  DIV
                
                        end
                        // step = 32
                        if(mul_div_counter == 31) begin
                            temp1[DATA_W-1:0] = temp2[DATA_W-1:0];                                   // temp1 = right half
                            output_nxt[DATA_W-1:0] = temp1[DATA_W-1:0] << 1;          
                            temp1[DATA_W-1:0] = temp2[2*DATA_W-1:DATA_W];                            // temp1 = left half
                            if(temp1[DATA_W-1:0] >= operand_b) begin
                                temp1[DATA_W-1:0] = temp1[DATA_W-1:0] - operand_b;
                                output_nxt[0] = 1;
                            end
                            output_nxt[2*DATA_W-1:DATA_W] = temp1[DATA_W-1:0];

                        end

                    end
	           		 default: output_nxt = 0;
    		    endcase
            end
		endcase
	end
    


    
    // Todo: output valid signal
    always @(*) begin
        if (state == S_ONE_CYCLE_OP || (state == S_MULTI_CYCLE_OP && mul_div_counter == 31)) begin        
            oDone_nxt = 1;
        end
        else begin                        
            oDone_nxt = 0;
        end
    end


	

    // Todo: Sequential always block
    always @(posedge i_clk or negedge i_rst_n) begin
        if (!i_rst_n) begin
            state       <= S_IDLE;
            operand_a   <= 0;
            operand_b   <= 0;
            inst        <= 0;
            mul_div_counter <= 0;
            oDone      <= 0;
            output_data      <= 0;

        end
        else begin
            state       <= state_nxt;
            operand_a   <= operand_a_nxt;
            operand_b   <= operand_b_nxt;
            inst        <= inst_nxt;
			mul_div_counter <= counter_nxt;
            oDone      <= oDone_nxt;
            output_data      <= output_nxt;
            
        end
    end
endmodule

module Cache#(
        parameter BIT_W = 32,
        parameter ADDR_W = 32,
        parameter block_size = 8
    )(
        input i_clk,
        input i_rst_n,
        // processor interface
            input i_proc_cen,
            input i_proc_wen,
            input [ADDR_W-1:0] i_proc_addr,
            input [BIT_W-1:0]  i_proc_wdata,
            output [BIT_W-1:0] o_proc_rdata,
            output o_proc_stall,
            input i_proc_finish,
            output o_cache_finish,
        // memory interface
            output o_mem_cen,
            output o_mem_wen,
            output [ADDR_W-1:0] o_mem_addr,
            output [BIT_W*4-1:0]  o_mem_wdata,
            input [BIT_W*4-1:0] i_mem_rdata,
            input i_mem_stall,
            output o_cache_available,
        // others
        input  [ADDR_W-1: 0] i_offset
    );

    integer i;

    assign o_cache_available = 1; // change this value to 1 if the cache is implemented

    //------------------------------------------//
    // //          default connection              //
    // assign o_mem_cen = i_proc_cen;              //
    // assign o_mem_wen = i_proc_wen;              //
    // assign o_mem_addr = i_proc_addr;            //
    // assign o_mem_wdata = i_proc_wdata;          //
    // assign o_proc_rdata = i_mem_rdata[0+:BIT_W];//
    // assign o_proc_stall = i_mem_stall;          //
    //------------------------------------------//

    // Todo: cache implementation
    // 1. cache memory
    reg     [BIT_W*4-1:0] mem1[0:block_size-1], mem2[0:block_size-1], mem1_nxt[0:block_size-1], mem2_nxt[0:block_size-1];
    reg     [24:0]        tag1[0:block_size-1], tag2[0:block_size-1], tag1_nxt[0:block_size-1], tag2_nxt[0:block_size-1];
    reg     valid1[0:block_size-1], valid2[0:block_size-1], valid1_nxt[0:block_size-1], valid2_nxt[0:block_size-1];
    reg                   tag_lru[0:block_size-1],tag_lru_nxt[0:block_size-1];
    // 2. rag int
    reg        chip_cen, chip_wen, chip_cen_nxt, chip_wen_nxt;
    reg [31:0] chip_addr, chip_wdata, chip_addr_nxt, chip_wdata_nxt;
    reg [31:0] memory_write_addr, memory_write_data, memory_write_addr_nxt, memory_write_data_nxt;
    
    //assign


    // ========  FSM  ==========
    // FSM based on operation cycles
    parameter S_INIT           = 3'd0;
    parameter S_READ_MISS      = 3'd1;
    parameter S_WRITE_HIT      = 3'd2;
    parameter S_WRITE_MISS     = 3'd3;
    parameter S_MEMREAD        = 3'd4;
    parameter S_CACHEWRITE     = 3'd5;
    parameter S_MEMWRITE       = 3'd6;
    parameter S_BUFFER         = 3'd7;
    
    reg     [3:0]       state, state_nxt;

    //true address (start from i_offset)
    wire [31:0] i_proc_addr_true;
    assign i_proc_addr_true = i_proc_addr - i_offset;

    wire hit;

    // hit
    assign hit = (( chip_cen && ( 
                        (valid1[chip_addr[6:4]] && chip_addr[31:7] == tag1[chip_addr[6:4]]) 
                     || (valid2[chip_addr[6:4]] && (chip_addr[31:7] == tag2[chip_addr[6:4]]))
                    ) 
                 ) || ( i_proc_cen && (
                        (valid1[i_proc_addr_true[6:4]] && i_proc_addr_true[31:7] == tag1[i_proc_addr_true[6:4]]) 
                     || (valid2[i_proc_addr_true[6:4]] && (i_proc_addr_true[31:7] == tag2[i_proc_addr_true[6:4]]))
                    )
                 )) ? 1'b1 : 1'b0;
 

    //chip related
    
    always @(*) begin
        if ((state == S_INIT || state == S_MEMREAD || state == S_CACHEWRITE || state == S_MEMWRITE) && i_proc_cen) begin
            chip_cen_nxt = i_proc_cen;
            chip_wen_nxt = i_proc_wen;
            chip_addr_nxt = i_proc_addr_true;
            chip_wdata_nxt = i_proc_wdata;
        end
        else if ((state != S_INIT && state_nxt == S_INIT) || state == S_WRITE_MISS || state == S_WRITE_HIT) begin
            chip_cen_nxt = 1'b0;
            chip_wen_nxt = 1'b0;
            chip_addr_nxt = 32'h0;
            chip_wdata_nxt = 32'h0;
        end
        else if(chip_cen && !chip_wen && hit) begin
            chip_cen_nxt = 1'b0;
            chip_wen_nxt = 1'b0;
            chip_addr_nxt = 32'h0;
            chip_wdata_nxt = 32'h0;
        end
        else begin
            chip_cen_nxt = chip_cen;
            chip_wen_nxt = chip_wen;
            chip_addr_nxt = chip_addr;
            chip_wdata_nxt = chip_wdata;
        end
    end

    //write buffer
    always @(*) begin
        if (state == S_WRITE_HIT || state == S_WRITE_MISS) begin
            memory_write_addr_nxt = chip_addr;
            memory_write_data_nxt = chip_wdata;
        end
        else if (state == S_MEMWRITE && state_nxt != S_MEMWRITE) begin
            memory_write_addr_nxt = 32'h0;
            memory_write_data_nxt = 32'h0;
        end
        else begin
            memory_write_addr_nxt = memory_write_addr;
            memory_write_data_nxt = memory_write_data;
        end
    end

    //mem access
    reg mem_cen, mem_wen;
    reg [31:0] mem_addr;
    reg [127:0] mem_wdata;
    assign o_mem_cen = mem_cen;
    assign o_mem_wen = mem_wen;
    assign o_mem_addr = mem_addr;
    assign o_mem_wdata = mem_wdata;

    always @(*) begin
        if (state_nxt == S_READ_MISS && state != S_READ_MISS) begin
            if(chip_cen) begin
                mem_cen = 1;
                mem_wen = 0;
                mem_addr = {chip_addr[31:4],4'b0} + i_offset;
                mem_wdata = 0;
            end
            else begin
                mem_cen = 1;
                mem_wen = 0;
                mem_addr = {i_proc_addr_true[31:4],4'b0} + i_offset;   
                mem_wdata = 0;
            end
        end
        else if (state == S_CACHEWRITE) begin
            mem_cen = 1;
            mem_wen = 1;
            mem_addr = {memory_write_addr[31:4],4'b0} + i_offset;
            mem_wdata = (tag1[memory_write_addr[6:4]] == memory_write_addr[31:7]) ? mem1[memory_write_addr[6:4]] : mem2[memory_write_addr[6:4]];
        end
        else if (state == S_WRITE_MISS) begin
            mem_cen = 1;
            mem_wen = 0;
            mem_addr = {chip_addr[31:4],4'b0} + i_offset;
            mem_wdata = 0;
        end
        else if (state == S_WRITE_HIT) begin
            mem_cen = 1;
            mem_wen = 1;
            mem_addr = {chip_addr[31:4],4'b0} + i_offset;
            mem_wdata = (tag1[chip_addr[6:4]] == chip_addr[31:7]) ? mem1[chip_addr[6:4]] : mem2[chip_addr[6:4]];
        end
        else begin
            mem_cen = 1'b0;
            mem_wen = 1'b0;
            mem_addr = 32'h0;
            mem_wdata = 32'h0;
        end
    end
    // cache data
    reg [2:0] cache_write_index;
    reg [24:0] cache_write_tag;
    reg [127:0] cache_write_data;

    always @(*) begin

        for (i=0; i<block_size; i=i+1) begin
                mem1_nxt[i] = mem1[i];
                mem2_nxt[i] = mem2[i];
                tag1_nxt[i] = tag1[i];
                tag2_nxt[i] = tag2[i];
                valid1_nxt[i] = valid1[i];
                valid2_nxt[i] = valid2[i];
                tag_lru_nxt[i] = tag_lru[i];
        end

        if(state == S_READ_MISS && state_nxt == S_INIT) begin
            cache_write_index = chip_addr[6:4];
            cache_write_tag = chip_addr[31:7];
            cache_write_data = i_mem_rdata;

            if( !valid1[cache_write_index] || (valid2[cache_write_index] && !tag_lru[cache_write_index]) ) begin
                mem1_nxt[cache_write_index] = cache_write_data;
                tag1_nxt[cache_write_index] = cache_write_tag ;
                valid1_nxt[cache_write_index] = 1'b1;
                tag_lru_nxt[cache_write_index] = 1'b1;// is recent

                mem2_nxt[cache_write_index] = mem2[cache_write_index];
                tag2_nxt[cache_write_index] = tag2[cache_write_index];
                valid2_nxt[cache_write_index] = valid2[cache_write_index];
            end
            else begin
                mem2_nxt[cache_write_index] = cache_write_data;
                tag2_nxt[cache_write_index] = cache_write_tag ;
                valid2_nxt[cache_write_index] = 1'b1;
                tag_lru_nxt[cache_write_index] = 1'b0;// is recent

                mem1_nxt[cache_write_index] = mem1[cache_write_index];
                tag1_nxt[cache_write_index] = tag1[cache_write_index];
                valid1_nxt[cache_write_index] = valid1[cache_write_index];
            end
        end
        else if(state_nxt == S_WRITE_HIT) begin
            if(i_proc_cen) begin
                cache_write_index = i_proc_addr_true[6:4];
                cache_write_tag = i_proc_addr_true[31:7];
                case (i_proc_addr_true[3:2]) 
                    2'b00: cache_write_data = (tag1[cache_write_index] == cache_write_tag) ?
                                                    {mem1[cache_write_index][127:32], i_proc_wdata} :
                                                    {mem2[cache_write_index][127:32], i_proc_wdata} ;
                    2'b01: cache_write_data = (tag1[cache_write_index] == cache_write_tag) ?
                                                    {mem1[cache_write_index][127:64], i_proc_wdata, mem1[cache_write_index][31:0]} :
                                                    {mem2[cache_write_index][127:64], i_proc_wdata, mem2[cache_write_index][31:0]} ;
                    2'b10: cache_write_data = (tag1[cache_write_index] == cache_write_tag) ?
                                                    {mem1[cache_write_index][127:96], i_proc_wdata, mem1[cache_write_index][63:0]} :
                                                    {mem2[cache_write_index][127:96], i_proc_wdata, mem2[cache_write_index][63:0]} ;
                    2'b11: cache_write_data = (tag1[cache_write_index] == cache_write_tag) ?
                                                    {i_proc_wdata, mem1[cache_write_index][95:0]} :
                                                    {i_proc_wdata, mem2[cache_write_index][95:0]} ;
                endcase
            end
            else begin
                cache_write_index = chip_addr[6:4];
                cache_write_tag = chip_addr[31:7];
                case (chip_addr[3:2]) 
                    2'b00: cache_write_data = (tag1[cache_write_index] == cache_write_tag) ?
                                                    {mem1[cache_write_index][127:32], chip_wdata} :
                                                    {mem2[cache_write_index][127:32], chip_wdata} ;
                    2'b01: cache_write_data = (tag1[cache_write_index] == cache_write_tag) ?
                                                    {mem1[cache_write_index][127:64], chip_wdata, mem1[cache_write_index][31:0]} :
                                                    {mem2[cache_write_index][127:64], chip_wdata, mem2[cache_write_index][31:0]} ;
                    2'b10: cache_write_data = (tag1[cache_write_index] == cache_write_tag) ?
                                                    {mem1[cache_write_index][127:96], chip_wdata, mem1[cache_write_index][63:0]} :
                                                    {mem2[cache_write_index][127:96], chip_wdata, mem2[cache_write_index][63:0]} ;
                    2'b11: cache_write_data = (tag1[cache_write_index] == cache_write_tag) ?
                                                    {chip_wdata, mem1[cache_write_index][95:0]} :
                                                    {chip_wdata, mem2[cache_write_index][95:0]} ;
                endcase
            end

            if( tag1[cache_write_index] == cache_write_tag ) begin
                mem1_nxt[cache_write_index] = cache_write_data;
                tag1_nxt[cache_write_index] = cache_write_tag ;
                valid1_nxt[cache_write_index] = 1'b1;
                tag_lru_nxt[cache_write_index] = 1'b1;// is recent

                mem2_nxt[cache_write_index] = mem2[cache_write_index];
                tag2_nxt[cache_write_index] = tag2[cache_write_index];
                valid2_nxt[cache_write_index] = valid2[cache_write_index];
            end
            else begin
                mem2_nxt[cache_write_index] = cache_write_data;
                tag2_nxt[cache_write_index] = cache_write_tag ;
                valid2_nxt[cache_write_index] = 1'b1;
                tag_lru_nxt[cache_write_index] = 1'b0;// is recent

                mem1_nxt[cache_write_index] = mem1[cache_write_index];
                tag1_nxt[cache_write_index] = tag1[cache_write_index];
                valid1_nxt[cache_write_index] = valid1[cache_write_index];
            end
        end
        else if (state == S_MEMREAD && state_nxt == S_CACHEWRITE) begin
            cache_write_index = memory_write_addr[6:4];
            cache_write_tag = memory_write_addr[31:7];
            case (memory_write_addr[3:2]) 
                2'b00: cache_write_data = {i_mem_rdata[127:32], memory_write_data};

                2'b01: cache_write_data = {i_mem_rdata[127:64], memory_write_data, i_mem_rdata[31:0]};
                                                
                2'b10: cache_write_data = {i_mem_rdata[127:96], memory_write_data, i_mem_rdata[63:0]};
                                                
                2'b11: cache_write_data = {memory_write_data, i_mem_rdata[95:0]};
                                              
            endcase
            if( !valid1[cache_write_index] || (valid2[cache_write_index] && !tag_lru[cache_write_index]) ) begin
                mem1_nxt[cache_write_index] = cache_write_data;
                tag1_nxt[cache_write_index] = cache_write_tag ;
                valid1_nxt[cache_write_index] = 1'b1;
                tag_lru_nxt[cache_write_index] = 1'b1;// is recent

                mem2_nxt[cache_write_index] = mem2[cache_write_index];
                tag2_nxt[cache_write_index] = tag2[cache_write_index];
                valid2_nxt[cache_write_index] = valid2[cache_write_index];
            end
            else begin
                mem2_nxt[cache_write_index] = cache_write_data;
                tag2_nxt[cache_write_index] = cache_write_tag ;
                valid2_nxt[cache_write_index] = 1'b1;
                tag_lru_nxt[cache_write_index] = 1'b0;// is recent

                mem1_nxt[cache_write_index] = mem1[cache_write_index];
                tag1_nxt[cache_write_index] = tag1[cache_write_index];
                valid1_nxt[cache_write_index] = valid1[cache_write_index];
            end
        end
        else begin
            cache_write_index = 0;
            cache_write_tag = 0;
            cache_write_data = 0;
        end
    end

    //output to chip
    reg chip_stall;
    reg [31:0] chip_rdata;
    assign o_proc_stall = chip_stall;
    assign o_proc_rdata = chip_rdata;

    always @(*) begin
        if(chip_cen && !chip_wen && hit) begin
            chip_stall = 1'b0;
            chip_rdata = (tag1[chip_addr[6:4]] == chip_addr[31:7]) ?
                            mem1[chip_addr[6:4]][32*(chip_addr[3:2]) +: 32] :
                            mem2[chip_addr[6:4]][32*(chip_addr[3:2]) +: 32] ;
        end
        else if(state == S_READ_MISS && state_nxt == S_INIT) begin
            chip_stall = 1'b0;
            chip_rdata = i_mem_rdata[32*(chip_addr[3:2]) +: 32];
        end
        else if(state == S_WRITE_HIT || state == S_WRITE_MISS) begin
            chip_stall = 1'b0;
            chip_rdata = 32'b0;
        end
        else begin
            chip_stall = 1'b1;
            chip_rdata = 32'b0;
        end
    end

    //finish signal
    assign o_cache_finish = (i_proc_finish && state == S_INIT) ? 1'b1 : 1'b0 ;

    //nxt state
    always @(*) begin
        case (state)
            S_INIT: begin
                if(i_proc_cen && i_proc_wen && hit)
                    state_nxt = S_WRITE_HIT;
                else if(i_proc_cen && !i_proc_wen && !hit)
                    state_nxt = S_READ_MISS;
                else if(i_proc_cen && i_proc_wen && !hit)
                    state_nxt = S_WRITE_MISS;
                else
                    state_nxt = S_INIT;
            end
            S_READ_MISS: begin
                if(!i_mem_stall)
                    state_nxt = S_INIT;
                else
                    state_nxt = S_READ_MISS;    
            end
            S_WRITE_HIT: begin
                state_nxt = S_MEMWRITE;
            end
            S_WRITE_MISS: begin
                state_nxt = S_MEMREAD;
            end
            S_MEMREAD: begin
                if(!i_mem_stall)
                    state_nxt = S_CACHEWRITE;
                else
                    state_nxt = S_MEMREAD;
            end
            S_CACHEWRITE: begin
                state_nxt = S_MEMWRITE;
            end
            S_MEMWRITE: begin
                if(i_mem_stall)
                    state_nxt = S_MEMWRITE;
                else if(((chip_cen && chip_wen)||(i_proc_cen && i_proc_wen)) && hit)
                    state_nxt = S_WRITE_HIT;
                else if(((chip_cen && !chip_wen)||(i_proc_cen && !i_proc_wen)) && !hit)
                    state_nxt = S_BUFFER;
                else if(((chip_cen && chip_wen)||(i_proc_cen && i_proc_wen)) && !hit)
                    state_nxt = S_WRITE_MISS;
                else
                    state_nxt = S_INIT;
            end
            S_BUFFER: begin
                state_nxt = S_READ_MISS;
            end
            default: begin
                state_nxt = S_INIT;
            end

        endcase
    end

    //state updata
    always @(posedge i_clk or negedge i_rst_n) begin
        if (!i_rst_n) begin
            for (i=0; i<block_size; i=i+1) begin
                mem1[i] <= 0;
                mem2[i] <= 0;
                tag1[i] <= 0;
                tag2[i] <= 0;
                valid1[i] <= 0;
                valid2[i] <= 0;
                tag_lru[i] <= 0;
            end
            chip_cen <= 0;
            chip_wen <= 0;
            chip_addr <= 0;
            chip_wdata <= 0;
            memory_write_addr <= 0;
            memory_write_data <= 0;
            state <= S_INIT;
        end
        else begin
            for (i=0; i<block_size; i=i+1) begin
                mem1[i] <= mem1_nxt[i];
                mem2[i] <= mem2_nxt[i];
                tag1[i] <= tag1_nxt[i];
                tag2[i] <= tag2_nxt[i];
                valid1[i] <= valid1_nxt[i];
                valid2[i] <= valid2_nxt[i];
                tag_lru[i] <= tag_lru_nxt[i];
            end
            chip_cen <= chip_cen_nxt;
            chip_wen <= chip_wen_nxt;
            chip_addr <= chip_addr_nxt;
            chip_wdata <= chip_wdata_nxt;
            memory_write_addr <= memory_write_addr_nxt;
            memory_write_data <= memory_write_data_nxt;
            state <= state_nxt;
        end
    end


endmodule