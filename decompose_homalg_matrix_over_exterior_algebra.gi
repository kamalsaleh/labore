
# Read( "/usr/local/lib/gap4r8/local/labore/solving_two_sided_equation_over_comm_ring.gi" );
# Read( "/usr/local/lib/gap4r8/local/labore/decompose_homalg_matrix_over_exterior_algebra.gi" );

LoadPackage( "ModulePresen" );
LoadPackage( "RingsForHomalg" );

DeclareGlobalFunction( "MyList" );

InstallGlobalFunction( MyList, 

function ( n )
local f, new_l,l;

l := Combinations( [ 0 ..n ] );

f := function( l, m )
local new_l;

new_l:= List( l, function( e )
                
                if Length( e ) = m then 
                
                   return e;
                   
                else 
                
                   return [ ];
                   
                fi;
                
                end );
new_l := Set( new_l );
Remove( new_l, 1 );

return new_l;

end;

new_l := List( [ 1 .. n+1 ], m-> f( l, m ) );

Add( new_l, [ [ ] ], 1 );

return Concatenation( new_l );

end );

DeclareGlobalFunction( "RingElement" );

InstallGlobalFunction( RingElement, 

function( l, R )

local f, s,i;

f := RingElementConstructor( R );

s := "1*";

for i in l do 

s := Concatenation( s, "e",String( i ), "*" );

od;

s:= Concatenation( s, "1" );

return f( s, R );

end );


DeclareGlobalFunction( "DecomposeRingElement" );

InstallGlobalFunction( DecomposeRingElement, 

function( d )
local R, n, l, coeff_list, dd, reduction_element, coeff_element, dd_new, u,v;

dd := ShallowCopy( d );

R := d!.ring;

n := Length( IndeterminatesOfExteriorRing( R ) ) -1;

l := MyList( n );

coeff_list := [ ];

for u in l do 

  v := [ 0..n ];
  
  SubtractSet( v, u );
  
  reduction_element := RingElement( v, R );
  
  dd_new := dd*reduction_element;
    
  coeff_element := dd_new/ RingElement( Concatenation( u, v ), R );
 
  Add( coeff_list, [ u, coeff_element ] );
  
  dd := dd - coeff_element*RingElement( u, R );
   
od;

return coeff_list;

end );

DeclareAttribute( "DecompositionOfHomalgMat", IsHomalgMatrix );

InstallMethod( DecompositionOfHomalgMat, 
                 [ IsHomalgMatrix ],
function( d )
local R, n, l, coeff_list, dd, reduction_element, coeff_element, dd_new, u,v, M, m,r;

dd := ShallowCopy( d );

R := d!.ring;

n := Length( IndeterminatesOfExteriorRing( R ) ) -1;

l := MyList( n );

coeff_list := [ ];

for u in l do 

  v := [ 0..n ];
  
  SubtractSet( v, u );
  
  reduction_element := RingElement( v, R );
  
  dd_new := dd*reduction_element;
  
  m := NrColumns( dd_new );
  
  r:= RingElement( Concatenation( u, v ), R );
  
  M := HomalgDiagonalMatrix( List( [ 1 .. m ], i -> r ), R );   
    
  coeff_element := RightDivide( dd_new, M );
 
  Add( coeff_list, [ u, coeff_element ] );
  
  dd := dd - coeff_element*RingElement( u, R );
   
od;

return coeff_list;

end );


# Very Solw, Need to be changed before being used anywhere....
DeclareAttribute( "DecompositionOfHomalgMatVersion2", IsHomalgMatrix );

InstallMethod( DecompositionOfHomalgMatVersion2, 
                 [ IsHomalgMatrix ],
function( M )
local R, zero_of_R, n, N, total_list, list_of_basis_indices;

R := HomalgRing( M );

zero_of_R := "0"/R;

n := Length( IndeterminatesOfExteriorRing( R ) ) -1;

N := EntriesOfHomalgMatrixAsListList( M );

total_list := List( N, row -> 
   List( row, current_element_in_row -> 
          [ Coefficients( current_element_in_row ), Coefficients( current_element_in_row )!.monomials ] 
       ) 
                  );
                  
list_of_basis_indices := MyList( n );

return  List( list_of_basis_indices,  function( index )
                                      local basis_index;
                                   
                                      basis_index := RingElement( index, R );
                                      
                                      return List( total_list, row-> List( row, function( current_element_in_row ) 
                                                                             
                                                                             if basis_index in current_element_in_row[ 2 ] then 
                                                                                 
                                                                                  return EntriesOfHomalgMatrixAsListList( current_element_in_row[ 1 ] )[ Position( current_element_in_row[ 2 ], basis_index ) ][ 1 ];
                                                                                  
                                                                             else 
                                                                             
                                                                                  return zero_of_R;
                                                                                  
                                                                             fi;
                                                                             
                                                                             end
                                                                             
                                                                      )
                                               );
                                                                      
                                      end
           
           );

end );

DeclareGlobalFunction( "RandomRingElement" );

InstallGlobalFunction( RandomRingElement, 

function( R )
local n, l, d, i; 

n := Length( IndeterminatesOfExteriorRing( R ) ) -1;

l := MyList( n );


d := RingElementConstructor( R )( "0", R );                                                          

for i in l do                                     

  d := d + Random( [ -10..10 ] )*RingElement( i, R );

od;

return d;

end );

DeclareGlobalFunction( "RandomHomalgMat" );

InstallGlobalFunction( RandomHomalgMat, 

function( m,n,R ) 

return HomalgMatrix( List( [ 1..m ], i-> List( [ 1..n ], j-> RandomRingElement( R ) ) ), m, n, R ) ;

end );


DeclareGlobalFunction( "FLeft" );
InstallGlobalFunction( FLeft,

function( sigma, A )
local S,n, basis_indices, zero_matrix,d, e_sigma;

S := A!.ring;
n := Length( IndeterminatesOfExteriorRing( S ) )-1;
basis_indices := MyList( n );

d := DecompositionOfHomalgMat( A );

zero_matrix := A - A;

e_sigma := RingElement( sigma, S );

return Iterated( List( basis_indices, function( tau )
                            local lambda, m;
                            
                            if ( not IsSubset( sigma, tau ) ) or ( IsSubset( tau, sigma ) and Length( tau ) > Length( sigma ) ) then 
                            
                                return zero_matrix;
                                
                            fi;
                            
                            if tau = sigma then 
                            
                                return d[ 1 ][ 2 ];
                                
                            fi;
                            
                            lambda := ShallowCopy( sigma );
                            
                            SubtractSet( lambda, tau );
                            
                            m := Position( basis_indices, lambda );
                            
                            return  ( ( RingElement( lambda, S )* RingElement( tau, S ) )/e_sigma )*d[ m ][ 2 ];
                            
                            end ), UnionOfColumns );
                     
end );
                     
                     

DeclareGlobalFunction( "FRight" );
InstallGlobalFunction( FRight,

function( sigma, A )
local S,n, basis_indices, zero_matrix,d, e_sigma;

S := A!.ring;
n := Length( IndeterminatesOfExteriorRing( S ) )-1;
basis_indices := MyList( n );

d := DecompositionOfHomalgMat( A );

zero_matrix := HomalgZeroMatrix( NrRows( A ), NrColumns( A ), S );

e_sigma := RingElement( sigma, S );

return Iterated( List( basis_indices, function( tau )
                            local lambda, m;
                            
                            if ( not IsSubset( sigma, tau ) ) or ( IsSubset( tau, sigma ) and Length( tau ) > Length( sigma ) ) then 
                            
                                return zero_matrix;
                                
                            fi;
                            
                            if tau = sigma then 
                            
                                return d[ 1 ][ 2 ];
                                
                            fi;
                            
                            lambda := ShallowCopy( sigma );
                            
                            SubtractSet( lambda, tau );
                            
                            m := Position( basis_indices, lambda );
                            
                            return  ( RingElement( tau, S )*( RingElement( lambda, S ) )/e_sigma )*d[ m ][ 2 ];
                            
                            end ), UnionOfRows );
                     
end );


DeclareGlobalFunction( "F2" );
InstallGlobalFunction( F2,

 function( sigma, A, B )
 
 local R, r,s, AA, BB, Is_Kronecker_AA, BB_Kronecker_Ir; 
 
 R := A!.ring;
 
 r := NrRows( A );
 s := NrColumns( B );
 
 AA := FLeft( sigma, A );
 BB := FRight( sigma, B );
 
 Is_Kronecker_AA :=  KroneckerMat( HomalgIdentityMatrix( s, R ), AA );
 BB_Kronecker_Ir :=  KroneckerMat( HomalgTransposedMat( BB ), HomalgIdentityMatrix( r, R ) );
 
 return UnionOfColumns( Is_Kronecker_AA, BB_Kronecker_Ir );
 
 end );


DeclareGlobalFunction( "F3" );
InstallGlobalFunction( F3, 

function( A, B )
local S, n, basis_indices;

S := A!.ring;
n := Length( IndeterminatesOfExteriorRing( S ) )-1;
basis_indices := MyList( n );

return UnionOfRows( List( basis_indices, sigma -> F2( sigma, A, B ) ) );

end );


DeclareGlobalFunction( "SolveTwoSidedEquationOverExteriorAlgebra" );
InstallGlobalFunction( SolveTwoSidedEquationOverExteriorAlgebra,

function( A, B, C )
local C_deco, C_deco_list, C_deco_list_vec, C_vec, N, sol, Q, R, l, m, s, r, n, XX, YY, XX_, YY_, X_, Y_, basis_indices;

R := A!.ring;

l := Length( IndeterminatesOfExteriorRing( R ) );
basis_indices := MyList( l-1 );

Q := CoefficientsRing( R ); 

C_deco := DecompositionOfHomalgMat( C );

C_deco_list := List( C_deco, i-> i[ 2 ] );

C_deco_list_vec := List( C_deco_list, c-> UnionOfRows( List( [ 1..NrColumns( C ) ], i-> CertainColumns( c, [ i ] ) ) ) );

C_vec := Q*UnionOfRows( C_deco_list_vec );

N := Q*F3( A, B );

sol := LeftDivide( N, C_vec );

if sol = fail then 

  return fail;
  
fi;

r := NrRows( A );
m := NrColumns( A );
s := NrColumns( C );
n := NrRows( B );

XX := CertainRows( sol, [ 1..m*s*2^l ] );

YY := CertainRows( sol, [ 1+ m*s*2^l ..( m*s+r*n)*2^l] );


XX_ := UnionOfColumns( List( [ 1 .. s ], i -> CertainRows( XX, [ ( i - 1 )*m*2^l + 1 .. i*m*2^l ] ) ) );
YY_ := UnionOfColumns( List( [ 1 .. n*2^l ], i -> CertainRows( YY, [ ( i - 1 )*r + 1 .. i*r ] ) ) );

X_ := Sum( List( [ 1..2^l ], i-> ( R*CertainRows( XX_, [ ( i - 1 )*m + 1 .. i*m ] ) )* RingElement( basis_indices[ i ], R ) ) );
Y_ := Sum( List( [ 1..2^l ], i-> (R*CertainColumns( YY_, [ ( i - 1 )*n + 1 .. i*n ] ) )* RingElement( basis_indices[ i ], R ) ) );

return [ X_, Y_ ];

end );
########################################

# gap> A := EntriesOfHomalgMatrixAsListList( A );
# [ [ 4*e0*e1*e2+4*e0*e1-8*e0*e2-8*e1*e2-5*e0+5*e1-e2-9 ], [ 6*e0*e1*e2-10*e0*e1+10*e0*e2-9*e1*e2+3*e0+10*e1-6*e2-3 ] ]
# gap> XX := EntriesOfHomalgMatrixAsListList( XX );
# [ [ -5*e0*e1*e2-7*e0*e1+8*e0*e2-5*e1*e2-e0-5*e1+2*e2-10, -2*e0*e1*e2+5*e0*e2-9*e1*e2-4*e0-10*e1+e2 ] ]
# gap> YY := EntriesOfHomalgMatrixAsListList( YY );
# [ [ 9*e0*e1*e2-e0*e1-9*e0*e2-4*e1*e2+9*e0+10*e1+2*e2-3 ], [ 4*e0*e1*e2-5*e0*e1-e0*e2+5*e1*e2+9*e0-10*e1+5*e2+5 ] ]
# gap> B := EntriesOfHomalgMatrixAsListList( B );  
# [ [ -7*e0*e1*e2-4*e0*e1+2*e0*e2+3*e1*e2+5*e0+7*e1-9*e2-7, -5*e0*e1*e2-10*e0*e1+7*e0*e2-9*e1*e2+9*e0-5*e1-6*e2-9 ] ]
# gap> C := EntriesOfHomalgMatrixAsListList( C );
# [ [ -18*e0*e1*e2+85*e0*e1-37*e0*e2+45*e1*e2-19*e0-96*e1+5*e2+111, -318*e0*e1*e2-26*e0*e1-66*e0*e2+89*e1*e2-72*e0+15*e1-9*e2+27 ], 
#   [ -18*e0*e1*e2+244*e0*e1-213*e0*e2+130*e1*e2-65*e0+20*e1-26*e2-5, 3*e0*e1*e2+50*e0*e1-91*e0*e2-28*e1*e2-24*e0+95*e1-78*e2-45 ] ]
# 
#  
# gap> A := EntriesOfHomalgMatrixAsListList( A );      
# [ [ 6*e0*e1*e2-9*e0*e1-4*e0*e2+9*e1*e2-e0+6*e2-8, -5*e0*e1*e2-8*e0*e1-2*e0*e2+7*e1*e2+5*e0-9*e1+5*e2+10 ], 
#   [ 6*e0*e1*e2+10*e0*e1+3*e0*e2+5*e1*e2+2*e0-9*e1+5*e2+5, -3*e0*e1*e2-3*e0*e1+7*e0*e2-3*e1*e2+e0+e1-2*e2+6 ] ]
# gap> XX := EntriesOfHomalgMatrixAsListList( XX );
# [ [ -10*e0*e1*e2+2*e0*e1+8*e0*e2-3*e1*e2-8*e0-e1+9*e2-2, -4*e0*e1*e2+e0*e1-4*e0*e2-10*e1*e2+7*e0-10*e1+6*e2+6 ], 
#   [ 2*e0*e1*e2-5*e0*e1-7*e0*e2+e1*e2+2*e1-e2-10, -3*e0*e1*e2+6*e0*e1-4*e0*e2+6*e1*e2+5*e0+4*e1-5*e2+8 ] ]
# gap> YY := EntriesOfHomalgMatrixAsListList( YY );
# [ [ 7*e0*e1*e2+7*e0*e1+9*e0*e2-5*e1*e2-4*e0-3*e1-4*e2-1, -6*e0*e1*e2-7*e0*e1-e0*e2+8*e1*e2+7*e0-2*e1-2*e2-10 ], 
#   [ -e0*e1*e2+6*e0*e1+e0*e2-8*e1*e2-4*e1+e2, -3*e0*e1*e2+2*e0*e1+3*e0*e2+4*e1*e2+7*e0-2*e1-5*e2+2 ] ]
# gap> B := EntriesOfHomalgMatrixAsListList( B );
# [ [ 7*e0*e1*e2-e0*e1+4*e1*e2+e0+10*e1-3*e2+9, -e0*e1*e2+4*e0*e1-e0*e2+8*e1*e2+7*e0+9*e1+9*e2-10 ], 
#   [ -8*e0*e1+3*e0*e2-8*e1*e2+10*e0+2*e1-4, -9*e0*e1*e2-6*e0*e1+3*e0*e2+5*e1*e2+4*e0-7*e1+6*e2 ] ]
# gap> C := EntriesOfHomalgMatrixAsListList( C );
# [ [ -75*e0*e1*e2+212*e0*e1+19*e0*e2+3*e1*e2-149*e0+69*e1-169*e2-53, 43*e0*e1*e2-61*e0*e1-223*e0*e2+310*e1*e2+21*e0+139*e1-51*e2+42 ], 
#   [ 106*e0*e1*e2-14*e0*e1+31*e0*e2-154*e1*e2-62*e0-9*e1+78*e2-78, 119*e0*e1*e2+34*e0*e1+63*e0*e2-11*e1*e2+93*e0-46*e1+16*e2+78 ] ]

 
 
 
 
 