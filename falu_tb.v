`timescale 1ns / 1ps
//////////////////////////////////////////////////////////////////////////////////
// Company: 
// Engineer: 
// 
// Create Date: 02/08/2025 07:26:34 PM
// Design Name: 
// Module Name: falu_tb
// Project Name: 
// Target Devices: 
// Tool Versions: 
// Description: 
// 
// Dependencies: 
// 
// Revision:
// Revision 0.01 - File Created
// Additional Comments:
// 
//////////////////////////////////////////////////////////////////////////////////


module falu_tb();
 parameter WIDTH = 32;
    parameter MANTISSA = 23;
    parameter EXP_BITS = WIDTH - MANTISSA - 1;

    // Testbench Inputs and Outputs
    reg [WIDTH-1:0] A,B;
    reg[2:0] sel;
    wire [WIDTH-1:0] result;
    wire overflow,underflow;

    // Instantiate the Floating Point Multiplier
    falu #(WIDTH, MANTISSA, EXP_BITS) DUT ( A , B,sel,result,overflow,underflow);

    // Test Stimulus
    initial begin
        // Monitor Outputs
        $monitor("Time = %0t | Input1 = %h | Input2 = %h | select =%b | Result = %h | Overflow = %b | Underflow = %b", 
                 $time, A, B,sel, result, overflow, underflow);

        // Test Case 1: Normal multiplication
        sel = 3'b000;
        A = 32'h00000000; // Positive normalized number
        B = 32'h00000000; // Negative normalized number
         #20;
        sel = 3'b101;
        A = 32'h41234021; // Example normalized number
        B = 32'h40214021; // Example normalized number
        #20;

        // Test Case 2: Positive number * Negative number
        sel = 3'b101;
        A = 32'h0F463821; // Positive normalized number
        B = 32'h0E400854; // Negative normalized number
        #20;
        
        sel = 3'b101;
        A = 32'h01301234; // Denormalized number
        B = 32'h01204356; // Denormalized number
        #20;
        sel = 3'b101;
        A = 32'h00000000; // Positive normalized number
        B = 32'h00000000; // Negative normalized number
         #20;
        sel = 3'b101;
        A = 32'h41234021; // Example normalized number
        B = 32'h40214021; // Example normalized number
        #20;

        // Test Case 2: Positive number * Negative number
        sel = 3'b101;
        A = 32'h0F463821; // Positive normalized number
        B = 32'h0E400854; // Negative normalized number
        #20;
        
        sel = 3'b101;
        A = 32'h41301234; // Denormalized number
        B = 32'h41204356; // Denormalized number
        #20;
        // Test Case 3: Multiplication with underflow
        sel = 3'b101;
        A = 32'h00231023; // Very small number
        B = 32'h0020C213; // Very small number
        #20;

        // Test Case 4: Multiplication with overflow
        sel = 3'b101;
        A = 32'h7E007E00; // Very large number
        B = 32'h7E007E00; // Very large number
        #20;

        // Test Case 5: Multiplication with zero
        sel = 3'b101;
        A = 32'h00000000; // Zero
        B = 32'h41234123; // Normalized number
        #20;

        // Test Case 6: Multiplication of two zeros
        sel = 3'b101;
        A = 32'h1F308900; // Zero
        B = 32'h12300420; // Zero
        #20;

        // Test Case 7: Multiplication of denormalized numbers
        sel = 3'b101;
        A = 32'h01301234; // Denormalized number
        B = 32'h01204356; // Denormalized number
        #20;

        // Stop simulation
        $finish;
    end


endmodule
