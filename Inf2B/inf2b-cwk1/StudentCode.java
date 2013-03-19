package imult;
/*
 * Class StudentCode: class for students to implement 
 * the specific methods required by the assignment:
 * add()
 * sub()
 * koMul()
 * (See coursework handout for full method documentation)
 */

import java.io.*;

public class StudentCode {
  public static BigInt add(BigInt A, BigInt B) 
  {
    int length_a = A.length();
    int length_b = B.length();
    if (length_b >= length_a)
    {
        BigInt c = B;B = A;A = c;
    }
    //swap if B > A in order to carry on without any problems in terms of the length
    //however considering that getDigit(i) returns 0, it doesn't really matter
    BigInt answer = new BigInt();
    length_a = A.length();
    length_b = B.length();
    Unsigned c = new Unsigned(0);
    for(int i = 0; i<length_a; i++)
    {
        DigitCarry d = Arithmetic.addDigits(A.getDigit(i),B.getDigit(i),c);
        Unsigned digit = d.digit();
        answer.setDigit(i,digit);
        c = d.carry();
    }
    //loop over the bigger bigger integer and keep adding and storing the carry
    //in c and the final result in answer.
    //If the value of c is not zero after the for loop, we put the carry to be
    //the most significant digit
    if(c.value()!=0)
    {
            answer.setDigit(length_a,c);
    }

    return answer;
  }
  public static BigInt sub(BigInt A, BigInt B) 
  {
    int length_a = A.length();
    int length_b = B.length();
    Unsigned c = new Unsigned(0);
    BigInt answer = new BigInt();
    //Loop over the length of the bigger number and keep substracting and
    //adding digits to the answer
    for(int i = 0; i<length_a; i++)
    {
        DigitCarry d = Arithmetic.subDigits(A.getDigit(i),B.getDigit(i),c);
        Unsigned digit = d.digit();
        answer.setDigit(i, digit);
        c = d.carry();
    }
    return answer;
  }
  public static BigInt koMul(BigInt A, BigInt B)
  {
      int a = A.length();
      int b = B.length();
      BigInt answer = new BigInt();
      //if both digits have length smaller or equal to one just use mulDigits
      //and return the product
      if (a <= 1 && b <= 1)
      {
          DigitCarry d = Arithmetic.mulDigits(A.getDigit(0), B.getDigit(0));
          Unsigned second = d.digit();
          Unsigned first = d.carry();
          answer.setDigit(0,second);
          if (first.value() != 0)
          {
              answer.setDigit(1,first);
          }
          return answer;
      }
      else
      {
          //if that's not the case, split the numbers according to the Karatsuba
          //algorightm and recursively find l, h, m. Then shift and get the final
          //result
          int n = Math.max((int)(Math.floor(A.length()/2)) , (int)(Math.floor(B.length()/2)));
          BigInt A1 = A.split(0,n-1);
          BigInt A2 = A.split(n,Math.max(a,b)+1);
          BigInt B1 = B.split(0,n-1);
          BigInt B2 = B.split(n,Math.max(a,b)+1);
          BigInt l = koMul(A1, B1);
          BigInt h = koMul(A2, B2);
          BigInt m = koMul(add(A1,A2),add(B1,B2));
          m = sub(m, l);
          m = sub(m, h);
          m.dump();
          m.lshift(n);
          h.lshift(2*n);
          answer = add(add(l, m), h);

          return answer;
      }
  }
  public static BigInt koMulOpt(BigInt A, BigInt B)
  {
      int a = A.length();
      int b = B.length();
      BigInt answer = new BigInt();
      if (Math.min(a,b) < 10)
      {
          //if the length of the smaller integer is smaller than 10 use schoolMul
          answer = Arithmetic.schoolMul(A, B);
          return answer;
      }
      else
      {
          //if not split the numbers and use recursion, however don't recurse with 
          //koMul, but use schoolMul instead of that.
          int n = Math.max((int)(Math.floor(A.length()/2)) , (int)(Math.floor(B.length()/2)));
          BigInt A1 = A.split(0,n-1);
          BigInt A2 = A.split(n,Math.max(a,b)+1);
          BigInt B1 = B.split(0,n-1);
          BigInt B2 = B.split(n,Math.max(a,b)+1);
          BigInt l = koMulOpt(A1, B1);
          BigInt h = koMulOpt(A2, B2);
          BigInt m = koMulOpt(add(A1,A2),add(B1,B2));
          m = sub(m, l);
          m = sub(m, h);
          m.dump();
          m.lshift(n);
          h.lshift(2*n);
          answer = add(add(l, m), h);

          return answer;
      } 
  }
  public static void main(String argv[])
  {
  }
}
