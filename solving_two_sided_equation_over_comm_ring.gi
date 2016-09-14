

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
 local list_of_rows, list_of_col_in_transposed_mat,m,n;
 
 m := NrRows( M );
 n := NrColumns( M );
 
 list_of_rows := List( [ 1 .. m ], i-> CertainRows( M, [ i ] ) );
 
 list_of_col_in_transposed_mat := List( list_of_rows, function( row )
                                          
                                          local list_of_columns_in_this_row, column;

                                          list_of_columns_in_this_row := List( [ 1 .. n ], j-> CertainColumns( row, [ j ] ) );
                                          
                                          column := UnionOfRows( list_of_columns_in_this_row );
                                          
                                          return column;
                                          
                                          end );
 return UnionOfColumns( list_of_col_in_transposed_mat );
 
 end );
                                          
  
##
InstallMethod( SolveTwoSidedEquationSystemOverCommutativeRing,
                "returns fail or a matrix X such that AX+YB=C, for some forgotten matrix Y",
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
  
  m := NrColumns( A );
  
  n := NrRows( B );
  
  if sol = fail then 
  
     return fail;
     
  else
  
     return  
           [
              UnionOfColumns( List( [ 1 .. s ], i -> CertainRows( sol, [ ( i - 1 )*m + 1 .. i*m ] ) ) ),
              UnionOfColumns( List( [ 1 .. n ], i -> CertainRows( sol, [ m*s + ( i - 1 )*r + 1 .. m*s + i*r ] ) ) ) 
           ];
                     
     
  fi;
  
end );




# Example

S := HomalgFieldOfRationalsInSingular()*"x,y";;
A := HomalgMatrix( [ [ "x,y,x-y,4*x"] ], 2,2, S );
#! <A 2 x 2 matrix over an external ring>
Display( A );
#! x,  y, 
#! x-y,4*x

B := HomalgMatrix( [ [ "x*y,x,x+y,y"] ], 2,2, S );
#! <A 2 x 2 matrix over an external ring>
Display( B );
#! x*y, x
#! x+y, y

C := HomalgMatrix( [ [ "2*x^2*y+2*x*y+2*y^2,2*x^2+2*y^2,2*x^2*y-2*x*y^2+8*x^2+8*x*y,2*x^2+6*x*y" ] ], 2,2, S );
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









