`timescale 1ns / 1ps
//////////////////////////////////////////////////////////////////////////////////
// Company: 
// Engineer: 
// 
// Create Date: 02/08/2025 06:47:30 PM
// Design Name: 
// Module Name: falu
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


module falu #(parameter N=32, M=23, EB=N-M-1)(

    input [N-1:0] A,
    input [N-1:0] B,
    input [2:0] sel,
    output [N-1:0] result,
    output overflow, underflow
);

wire [N-1:0] B_neg;
reg [N-1:0] resultX;
assign B_neg = {~B[N-1], B[N-2:0]};
wire[N-1:0] resultA,resultS,resultM,resultD;
wire [2:0] resultC;
wire oA,uA,oS,uS,oM,uM,oD,uD;
fpa #(N, M, EB) DUT1 (A, B_neg, resultS, oS, uS);
fpa #(N, M, EB) DUT2 (A, B, resultA, oA, uA);
fpm #(N,M,EB) DUT3 (A,B,resultM,oM,uM);
fpc #(N,M,EB) DUT4 (A,B,resultC);
fpd1 #(N,M,EB) DUT5 (A,B,resultD,oD,uD);
always@(*)
begin
if(sel==1)
    begin
    resultX = resultA;
    end
else if(sel==2)
    begin
    resultX = resultS;
    end
else if(sel==3)
    begin
    resultX = resultM;
    end
else if(sel==4)
    begin
    resultX = resultD;
    end
else if(sel==5)
    begin
    resultX = resultC;
    end   
else 
    begin
    resultX = 0;
    end
end
assign overflow = oA || oS ||oM || oD ;
assign underflow = uA || uS ||uM || uD;
assign result = resultX;
endmodule

//floating point comparator
module fpc #(parameter N=32,M=23,EB=N-M-1)(
input[N-1:0] A1,B1,
output [2:0] result );
wire signA,signB;
wire [N-2:M] expA,expB;
wire [M-1:0] MantA,MantB;
wire [EB:0] expdiff;
wire [M:0] Mantdiff;
reg g,l,e;
assign expdiff = A1[N-2:M] - B1[N-2:M];
assign Mantdiff = A1[M-1:0] - B1[M-1:0];
assign signA = A1[N-1];
assign signB = B1[N-1];
assign expA = A1[N-2:M];
assign expB = B1[N-2:M];
assign MantA = A1[M-1:0];
assign MantB = B1[M-1:0];
always@(*)
begin
if((signA^signB))
begin
if(!signA && signB)
begin
g = 1'b1;
l = 1'b0;
e = 1'b0;
end
else
begin
g = 1'b0;
l = 1'b1;
e = 1'b0;
end
end
else
begin
if(!(expA^expB))
begin
if(!(MantA^MantB))
begin
g = 1'b0;
l = 1'b0;
e = 1'b1;
end
else
begin
g = (Mantdiff[M])?1'b0:1'b1;
l= (Mantdiff[M])?1'b1:1'b0;
e = 1'b0;
end
end
else
begin
g = (expdiff[EB])?1'b0:1'b1;
l= (expdiff[EB])?1'b1:1'b0;
e = 1'b0;
end
end
end
assign result = {g,l,e};
endmodule

//floating point adder

module fpa #(parameter N=32, M=23, EB=N-M-1)(

    input [N-1:0] A,
    input [N-1:0] B,
    output [N-1:0] result,
    output overflow, underflow
);
reg signA, signB, signR;
reg [EB-1:0] expA, expB, expR;
reg [M:0] mantA, mantB;
reg [M+1:0] mantR;
reg [EB-1:0] expdiff;
reg [N-1:0] resultD;
reg o1,u1;
always @(*) begin
    signA = A[N-1];
    signB = B[N-1];
    expA = A[N-2:M];
    expB = B[N-2:M];
    mantA = {1'b1, A[M-1:0]};
    mantB = {1'b1, B[M-1:0]};

    if (A == 0 && B == 0) begin
        resultD = 0;
        u1=1;
    end else if(expA>=8'hff && expB>=8'hff)
    begin
    o1 = 1;
    end else begin
        if (expA > expB) begin
            expdiff = expA - expB;
            mantB = mantB >> expdiff;
            expR = expA;
             end
       else 
          begin
            expdiff = expB - expA;
            mantA = mantA >> expdiff;
            expR = expB;
        end

         if (signA == signB) begin
            mantR = mantA + mantB;
            signR = signA;
        end else begin
            if (mantA > mantB) begin
                mantR = mantA - mantB;
                signR = signA;
            end else begin
                mantR = mantB - mantA;
                signR = signB;
            end
        end

                if (mantR[M+1] == 1) begin mantR = mantR >> 1; expR = expR + 1;end 
                else if (mantR[M] == 1) begin mantR=mantR;expR=expR;end
                else if (mantR[M-1]) begin mantR = mantR << 1; expR = expR - 1; end
                else if (mantR[M-2]) begin mantR = mantR << 2; expR = expR - 2; end
                else if (mantR[M-3]) begin mantR = mantR << 3; expR = expR - 3; end
                else if (mantR[M-4]) begin mantR = mantR << 4; expR = expR - 4; end
                else if (mantR[M-5]) begin mantR = mantR << 5; expR = expR - 5; end
                else if (mantR[M-6]) begin mantR = mantR << 6; expR = expR - 6; end
                else if (mantR[M-7]) begin mantR = mantR << 7; expR = expR - 7; end
                else if (mantR[M-8]) begin mantR = mantR << 8; expR = expR - 8; end
                else if (mantR[M-9]) begin mantR = mantR << 9; expR = expR - 9; end
                else if (mantR[M-10]) begin mantR = mantR << 10; expR = expR - 10; end
                else if (mantR[M-11]) begin mantR = mantR << 11; expR = expR - 11; end
                else if (mantR[M-12]) begin mantR = mantR << 12; expR = expR - 12; end
                else if (mantR[M-13]) begin mantR = mantR << 13; expR = expR - 13; end
                else if (mantR[M-14]) begin mantR = mantR << 14; expR = expR - 14; end
                else if (mantR[M-15]) begin mantR = mantR << 15; expR = expR - 15; end
                else if (mantR[M-16]) begin mantR = mantR << 16; expR = expR - 16; end
                else if (mantR[M-17]) begin mantR = mantR << 17; expR = expR - 17; end
                else if (mantR[M-18]) begin mantR = mantR << 18; expR = expR - 18; end
                else if (mantR[M-19]) begin mantR = mantR << 19; expR = expR - 19; end
                else if (mantR[M-20]) begin mantR = mantR << 20; expR = expR - 20; end
                else if (mantR[M-21]) begin mantR = mantR << 21; expR = expR - 21; end
                else if (mantR[M-22]) begin mantR = mantR << 22; expR = expR - 22; end
                else if (mantR[M-23]) begin mantR = mantR << 23; expR = expR - 23; end
                else begin mantR = mantR<<24; expR = expR-24;end
            
       
 

    o1 = (expR >= 8'hFF) ? 1 : 0;
    u1 = (expR < 1) ? 1 : 0;

    if (o1) begin
        resultD = {signR, 8'hFF, 23'b0}; // Infinity
    end else if (u1) begin
        resultD = 32'h00000000; // Zero
    end else begin
        resultD = {signR, expR, mantR[M-1:0]};
    end
    end
end
assign result = resultD;
assign overflow = o1;
assign underflow = u1;
endmodule

// floating point multiplier
module fpm#(parameter WIDTH = 32, MANTISSA = 23, EXP_BITS = WIDTH - MANTISSA - 1) (
    input [WIDTH-1:0] Input1,
    input [WIDTH-1:0] Input2,
    output [WIDTH-1:0] Result,
    output Overflow,
    output Underflow
);
wire [(2 * MANTISSA) + 1:0] Mantissa_Product;
    wire [1:0] Exponent_Adjustment;
    wire [WIDTH-2:0] Computed_Result;

    
    Fixed_Point_Multiplier #(MANTISSA) Mantissa_Multiply (
        {1'b1, Input1[MANTISSA-1:0]}, 
        {1'b1, Input2[MANTISSA-1:0]}, 
        Mantissa_Product
    );

    
    assign Computed_Result[MANTISSA-1:0] = 
        (Mantissa_Product[(2 * MANTISSA) + 1]) ? 
        Mantissa_Product[2 * MANTISSA : MANTISSA + 1] : 
        Mantissa_Product[2 * MANTISSA - 1 : MANTISSA];

    
    Adder #(EXP_BITS) Exponent_Addition (
        Input1[WIDTH-2:MANTISSA], 
        Input2[WIDTH-2:MANTISSA], 
        Mantissa_Product[(2 * MANTISSA) + 1], 
        {Exponent_Adjustment, Computed_Result[WIDTH-2:MANTISSA]}
    );

   
    assign Overflow = ((~Exponent_Adjustment[1]) & Exponent_Adjustment[0]);
    assign Underflow = Exponent_Adjustment[1];

    
    assign Result[WIDTH-1] = Input1[WIDTH-1] ^ Input2[WIDTH-1];

    
    assign Result[WIDTH-2:0] = 
        Overflow ? {WIDTH{1'b1}} : 
        (Underflow ? {WIDTH{1'b0}} : Computed_Result);

endmodule


module Fixed_Point_Multiplier #(parameter MANTISSA = 10) (
    input [MANTISSA:0] Mant1,
    input [MANTISSA:0] Mant2,
    output [(2 * MANTISSA) + 1:0] Product
);
    assign Product = Mant1 * Mant2;
endmodule


module Adder #(parameter EXP_BITS = 5) (
    input [EXP_BITS-1:0] Exp1,
    input [EXP_BITS-1:0] Exp2,
    input Normalize_Shift,
    output [EXP_BITS+1:0] Adjusted_Exponent
);
    wire [EXP_BITS+1:0] Bias;

   
    assign Bias = -127; 
    assign Adjusted_Exponent = Exp1 + Exp2 + Bias + Normalize_Shift;
endmodule


//floating point divider

module fpd1 #(parameter N=32, M=23, EB=N-M-1)(
    input [31:0] A, 
    input [31:0] B, 
    output [31:0] result,
    output overflow,
    output underflow
);
    reg [N-1:0] AdjustedB;
    reg [N-1:0] Rc1, Rc2, Rc3,Rc4,Rc5,Rc6;
    reg [N-1:0] Product;
    reg o1, u1;
    
    always @(*) begin
        // Initialize flags
        o1 = 0;
        u1 = 0;

        // Handle special cases
        if (A == 0) begin
            Product = 0;
            u1 = 1;  // Underflow if A is zero
        end else if (B == 0) begin
            Product = 32'h7F800000; // IEEE-754 Infinity
            o1 = 1;  // Overflow (division by zero)
        end else if (A[N-2:M] >= 8'hFF || B[N-2:M] >= 8'hFF) begin
            o1 = 1; // Overflow for invalid IEEE-754 numbers
        end else begin
            // Normalize B for initial approximation
            AdjustedB = {B[31], 8'd126, B[22:0]}; 

            // Newton-Raphson Iteration for Reciprocal Approximation
            Rc1 = 32'h3F800000 - (AdjustedB >> 1);
            Rc2 = Rc1 * (32'h40000000 - (AdjustedB * Rc1) >> 23);
            Rc3 = Rc2 * (32'h40000000 - (AdjustedB * Rc2) >> 23);
             Rc4 = Rc3 * (32'h40000000 - (AdjustedB * Rc3) >> 23);
              Rc5 = Rc4 * (32'h40000000 - (AdjustedB * Rc4) >> 23);
               Rc6 = Rc5 * (32'h40000000 - (AdjustedB * Rc5) >> 23);

            // Final multiplication to get division result
            Product = (A * Rc6) >> 23; // Normalize multiplication result
        end
    end
    
    assign overflow = o1;
    assign underflow = u1;

    // Correct exponent calculation in result
    assign result = {Product[31], (A[30:23] - B[30:23] + 127), Product[22:0]};

endmodule
