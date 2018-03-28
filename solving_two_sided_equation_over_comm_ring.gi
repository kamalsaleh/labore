
# Read( "/usr/local/lib/gap4r8/local/labore/solving_two_sided_equation_over_comm_ring.gi" );


LoadPackage( "ModulePresen" );


DeclareOperation( "UnionOfRows", 
                  [ IsList ] );

DeclareOperation( "UnionOfColumns", 
                  [ IsList ] );
                  
DeclareOperation( "HomalgTransposedMat", 
                  [ IsHomalgMatrix ] );

DeclareOperation( "SolveTwoSidedEquationSystemOverCommutativeRing",
           
               [ IsHomalgMatrix, IsHomalgMatrix, IsHomalgMatrix ] );

####################################################################

##                  
InstallMethod( UnionOfRows, 
               [ IsList ],
function( l )
local current_mat, mat;

if Length( l ) = 0 then 
  
  Error( "The given list is empty" );
  
fi;

return Iterated( l, UnionOfRows );

end );
                  
            
InstallMethod( UnionOfColumns, 
               [ IsList ],
function( l )
local current_mat, mat;

if Length( l ) = 0 then 
  
  Error( "The given list is empty" );
  
fi;

return Iterated( l, UnionOfColumns );

end );






InstallMethod( HomalgTransposedMat, 
                [ IsHomalgMatrix ], 
function( M )
  
  return HomalgMatrix( String( TransposedMat( EntriesOfHomalgMatrixAsListList( M ) ) ), NrColumns( M ), NrRows( M ), HomalgRing( M ) );
 
end );
                                          
  
##
InstallMethod( SolveTwoSidedEquationSystemOverCommutativeRing,
                "returns fail or a list of matrices [ X, Y ] such that A*X+Y*B=C",
               [ IsHomalgMatrix, IsHomalgMatrix, IsHomalgMatrix ],

  function( A, B, C )
  local R, r, s, AA, BB, AABB, CC, sol, m, n; 
  
  R := HomalgRing( A );
  
  r := NrRows( A );
  
  s := NrColumns( B );
  
  if not NrRows( C ) = r then 
  
     Error( "The number of rows of the first and last matrices should be equal" );
     
  elif not NrColumns( C ) = s then
    
     Error( "The number of columns of the second and last matrices should be equal" );
   
  fi;
  

  AA := KroneckerMat( HomalgIdentityMatrix( s, R ), A );
  
##### Here it works only for commutative rings...
  BB := KroneckerMat( HomalgTransposedMat( B ), HomalgIdentityMatrix( r, R ) );
#####

  AABB := UnionOfColumns( AA, BB );
  
  CC := UnionOfRows( List( [ 1 .. s ], i-> CertainColumns( C, [ i ] ) ) );
  
  sol:= LeftDivide( AABB, CC );
  
  if sol = fail then 
  
     return fail;
     
  else
  
     
     m := NrColumns( A );
  
     n := NrRows( B );
  
     return  
           [
              UnionOfColumns( List( [ 1 .. s ], i -> CertainRows( sol, [ ( i - 1 )*m + 1 .. i*m ] ) ) ),
              UnionOfColumns( List( [ 1 .. n ], i -> CertainRows( sol, [ m*s + ( i - 1 )*r + 1 .. m*s + i*r ] ) ) ) 
           ];
                     
     
  fi;
  
end );

# The following function finds elements x_1,....,x_n in the commutative ring R such that 
# x1*l[1] + ... + x_n*l[n] = C mod B, i.e., 
# such that the equation x1*l[1] + ... + x_n*l[n] +Z*B = C is solvable.
# n is length of l.
solve := 
  function( l, B, C, R)
  local vec, main; 

  vec := function( H ) return Iterated( List( [ 1 .. NrColumns( H ) ], i -> CertainColumns( H, [ i ] ) ), UnionOfRows ); end;
  main := UnionOfColumns( Iterated( List( l,vec ), UnionOfColumns ), KroneckerMat( HomalgIdentityMatrix(NrColumns( C ), R ), B ) ); 
  return CertainRows( LeftDivide( main, vec(C)), [ 1 .. Length( l ) ] );

end;

# Example of a two sided equation over Q[ x,y ]

S := HomalgFieldOfRationalsInSingular()*"x,y";;
A := HomalgMatrix( [ [ "x,y,x-y,4*x"] ], 2, 2, S );
#! <A 2 x 2 matrix over an external ring>
Display( A );
#! x,  y, 
#! x-y,4*x

B := HomalgMatrix( [ [ "x*y,x,x+y,y"] ], 2, 2, S );
#! <A 2 x 2 matrix over an external ring>
Display( B );
#! x*y, x
#! x+y, y

C := HomalgMatrix( [ [ "2*x^2*y+2*x*y+2*y^2,2*x^2+2*y^2,2*x^2*y-2*x*y^2+8*x^2+8*x*y,2*x^2+6*x*y" ] ], 2, 2, S );
#! <A 2 x 2 matrix over an external ring>
Display( C );
#! 2*x^2*y+2*x*y+2*y^2,        2*x^2+2*y^2,
#! 2*x^2*y-2*x*y^2+8*x^2+8*x*y,2*x^2+6*x*y

sol := SolveTwoSidedEquationSystemOverCommutativeRing( A, B, C );
#! [ <An unevaluated 2 x 2 matrix over an external ring>, <An unevaluated 2 x 2 matrix over an external ring> ]
XX := sol[ 1 ];
#! <An unevaluated 2 x 2 matrix over an external ring>
YY := sol[ 2 ];
#! <An unevaluated 2 x 2 matrix over an external ring>
A * XX + YY * B = C;
#! true
Display( XX );
#! 2*x*y,2*x,
#! 0,    0   
Display( YY );
#! 0,2*y,
#! 0,8*x 


## Example of a two sided equation over Z

R := HomalgRingOfIntegers( );
#! Z
B := HomalgMatrix( [ [ 3, 12, 40 ], [ 35 , 6, 81 ] ], 2, 3, R );
#! <A 2 x 3 matrix over an internal ring>
A := HomalgMatrix( [ [ 2, 3 ],[ 4, 5 ], [ 65, 8 ] ], 3, 2, R ); 
#! <A 3 x 2 matrix over an internal ring>
Display( A );
#! [ [   2,   3 ],
#!  [   4,   5 ],
#!  [  65,   8 ] ]
Display( B );
#! [ [   3,  12,  40 ],
#!  [  35,   6,  81 ] ]
C := A * B+ A * B;
#! <An unevaluated 3 x 3 matrix over an internal ring>
Display( C );
#! [ [   222,    84,   646 ],
#!  [   374,   156,  1130 ],
#!  [   950,  1656,  6496 ] ]
sol := SolveTwoSidedEquationSystemOverCommutativeRing( A, B, C );
#! [ <An unevaluated 2 x 3 matrix over an internal ring>, <An unevaluated 3 x 2 matrix over an internal ring> ]
XX := sol[ 1 ];
#! <An unevaluated 2 x 3 matrix over an internal ring>
YY := sol[ 2 ];
#! <An unevaluated 3 x 2 matrix over an internal ring>
Display( A * XX + YY * B );
#! [ [   222,    84,   646 ],
#!  [   374,   156,  1130 ],
#!  [   950,  1656,  6496 ] ]
Display( XX );
#! [ [    422379692,   -578496624,   -895867312 ],
#!  [  -3845376046,   3046120608,   1765040492 ] ]
Display( YY );
#! [ [   -854467938,    378707794 ],
#!  [  -1386332698,    619895998 ],
#!  [   1102776446,            0 ] ] 







