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
    fpa #(N, M, EB) DUT1 (A, B,1'b1, resultS, oS, uS);
    fpa #(N, M, EB) DUT2 (A, B,1'b0, resultA, oA, uA);
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
    input sel,
    output [N-1:0] result,
    output overflow, underflow
);
reg[M:0] mantA,mantB,mantS;
reg[M+1:0] mantR;
reg signR;
reg[4:0] count,shift,i;
reg [7:0] expR;
reg [31:0] resultD;
reg u1,o1;
 
always@(*)
    begin
    if((A[30:23]==0)&&(B[30:23]==0))
        begin
        u1=1'b1;
        end
     else
         begin
         u1=1'b0;
         end
      if((A[30:23]==8'hFF)||(B[30:23]==8'hFF))
        begin
        o1=1'b1;
        end
     else
         begin
         o1=1'b0;
         end  
         
     if(A[31]^B[31]^sel==1'b0)
        begin
        mantA={1'b1,A[22:0]};
        mantB={1'b1,B[22:0]};
            if(A[30:23]==B[30:23])
                begin
                    if(mantA>=mantB)
                        begin
                        mantR=mantA+mantB;
                        signR=A[31];
                        end
                        else
                            begin
                             mantR=mantA+mantB;
                             signR=B[31];
                            end
                        expR=A[30:23];
                end
             else if(A[30:23]>B[30:23])
                begin
                    mantB=mantB>>(A[30:23]-B[30:23]);
                    mantR=mantA+mantB;
                    expR=A[30:23];
                    signR=A[31];
                end
              else
                begin
                mantA=mantA>>(B[30:23]-A[30:23]);
                    mantR=mantA+mantB;
                    expR=B[30:23];
                    signR=B[31];
                end
              resultD=(mantR[24]==1)?({signR,expR+1,mantR[23:1]}):({signR,expR,mantR[22:0]});
        end 
      else
        begin
         mantA={1'b1,A[22:0]};
        mantB={1'b1,B[22:0]};
            if(A[30:23]==B[30:23])
                begin
                    if(mantA>mantB)
                        begin
                        mantS=mantA-mantB;
                        signR=A[31];
                        expR=A[30:23];
                        end
                        else if(mantA<mantB)
                            begin
                             mantS=mantB-mantA;
                             signR=B[31];
                             expR=B[30:23];
                            end
                        else
                            begin
                             mantS=mantB-mantA;
                             signR=A[31];
                             expR=A[30:23]-B[30:23];
                            end
                end
             else if(A[30:23]>B[30:23])
                begin
                    mantB=mantB>>(A[30:23]-B[30:23]);
                    mantS=mantA-mantB;
                    expR=A[30:23];
                    signR=A[31];
                end
              else
                begin
                mantA=mantA>>(B[30:23]-A[30:23]);
                    mantS=mantB-mantA;
                    expR=B[30:23];
                    signR=B[31];
                end
                count=0;
                for(i=23;i>0;i=i-1)
                begin
                if((mantS[i])&&(count==0))
                        begin
                            shift=23-i;
                            count=count+1;
                        end
                end
                
                mantS=mantS<<shift;
              resultD={signR,expR-shift,mantS[22:0]};
        end
     
    end
assign overflow=o1;
assign underflow = u1;
assign result=(o1||u1)?0:resultD;
endmodule
// floating point multiplier
module fpm#(parameter WIDTH = 32, M = 23, EB = WIDTH - M - 1) (

    input [WIDTH-1:0] A,
    input [WIDTH-1:0] B,
    output [WIDTH-1:0] result,
    output overflow,
    output underflow
);

reg[M:0] mantA,mantB;
reg[47:0] mantR;
reg[7:0] expR;
reg o1,u1,signR;
reg[31:0] resultD;
always@(*)
    begin
        if((A[30:23]==0)||(B[30:23]==0))
            u1=1'b1;
            else
            u1=1'b0;
        if((A[30:23]==8'hFF)||(B[30:23]==8'hFF))
            o1=1'b1;
            else if(A[30:23]+B[30:23]-127>8'hFF)
            o1=1'b1;
            else 
            o1=1'b0;
            
            
         mantA={1'b1,A[22:0]};
         mantB={1'b1,B[22:0]};
         signR=A[31]^B[31];
         expR=A[30:23] + B[30:23]-127;
         mantR=mantA*mantB;
         resultD=(mantR[47]==1'b1)?{signR,expR+1,mantR[46:24]}:{signR,expR,mantR[45:23]};
         
        
    end
    assign overflow=o1;
    assign underflow=u1;
    
    assign result=(o1||u1)?0:resultD;

endmodule


//floating point divider

                                                                                                                                                                      -
module fpd1 #(parameter N=32, M=23, EB=N-M-1)(

    input [31:0] A, 
    input [31:0] B, 
    output [31:0] result,
    output overflow,
    output underflow
);
    reg [24:0] Ab,t,Aa;
    reg [24:0] Rc0,Rc1, Rc2, Rc3, Rc4, Rc5, Rc6;
    reg [49:0] ProductA;
    reg [31:0] Product;
    reg o1, u1;
    reg[7:0] new_exp;
    reg[M-1:0] db;
    
    always @(*) begin
        // Initialize flags
        o1 = 0;
        u1 = 0;
        Product = 0;

        // Correct sign bit handling
        Product[31] = A[31] ^ B[31];

        // Handle special cases
        if (A == 32'h00000000) begin
            Product = 32'h00000000; // Zero divided by anything is zero
            u1 = 1;  
        end else if (B == 32'h00000000) begin
            Product = {A[31], 8'hFF, 23'h000000}; // IEEE-754 Infinity with correct sign
            o1 = 1;  
        end else if (A[N-2:M] >= 8'hFF || B[N-2:M] >= 8'hFF) begin
            o1 = 1; // Overflow for invalid IEEE-754 numbers
        end else begin
            // Normalize B for initial approximation
           Rc0=25'b00100000000000000000000000;
           t=25'b1000000000000000000000000;
           Ab={2'b01,B[22:0]};
           Aa={2'b01,A[22:0]};
           Rc1=(Rc0*(t-((Rc0*Ab)>>25)))>>25;
           Rc2=(Rc1*(t-((Rc1*Ab)>>25)))>>25;
           Rc3=(Rc2*(t-((Rc2*Ab)>>25)))>>25;
           Rc4=(Rc3*(t-((Rc3*Ab)>>25)))>>25;
           Rc5=(Rc4*(t-((Rc4*Ab)>>25)))>>25;
           Rc6=(Rc5*(t-((Rc5*Ab)>>25)))>>25;
           ProductA=Rc6*Aa;
           if(ProductA[49])
            begin
                Product[22:0] = ProductA[48:24];
                new_exp[7:0]=A[30:23]-B[30:23] + 127+1;
            end
            else
                begin
                Product[22:0] = ProductA[47:23];
                    new_exp[7:0]=A[30:23]-B[30:23] + 127;
                end
                
             if(A[31]^B[31])
                begin
                Product[31]=1'b1;
                end
              else
              begin
              Product[31]=1'b0;
              end
        end
    end
    
    assign overflow = o1;
    assign underflow = u1;
    

    // Correct exponent calculation with underflow/overflow handling
   

    assign result = (o1 | u1) ? Product : {Product[31], new_exp[7:0], Product[22:0]};

endmodule
