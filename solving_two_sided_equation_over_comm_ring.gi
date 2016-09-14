

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

if not ForAll( l, IsHomalgMatrix ) then 

  Error( "The list should contain only homalg matrices" );
  
fi;

current_mat := CertainRows( l[ 1 ], [ ] );

for mat in l do

current_mat := UnionOfRows( current_mat, mat );

od;

return current_mat;

end );
                  
            
InstallMethod( UnionOfColumns, 
               [ IsList ],
function( l )
local current_mat, mat;

if Length( l ) = 0 then 
  
  Error( "The given list is empty" );
  
fi;

if not ForAll( l, IsHomalgMatrix ) then 

  Error( "The list should contain only homalg matrices" );
  
fi;

current_mat := CertainColumns( l[ 1 ], [ ] );

for mat in l do

current_mat := UnionOfColumns( current_mat, mat );

od;

return current_mat;

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
  
  ## Here it works only for commutative rings...
  BB := KroneckerMat( HomalgTransposedMat( B ), HomalgIdentityMatrix( r, R ) );
  
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
QQ := HomalgFieldOfRationalsInSingular()*"x,y,z,w";
S := KoszulDualRing( QQ );

A := HomalgMatrix( [ [ "e0,e1,e2,1" ] ], 2,2, S );
B := HomalgMatrix( [ [ "e2,e1,e3,5*e0-e0*e3" ] ], 2,2, S );

XX := B;
YY := A*A;

C:= A*XX + YY*B;







