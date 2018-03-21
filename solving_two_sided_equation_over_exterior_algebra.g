LoadPackage( "RingsForHomalg" );

## function to compute the standard trasnpose of a homalg matrix

transposed_homalg_mat := 
    function( M )
    return HomalgMatrix( String( TransposedMat( EntriesOfHomalgMatrixAsListList( M ) ) ), NrColumns( M ), NrRows( M ), HomalgRing( M ) );
end;

standard_list_of_basis_indices := n -> Concatenation( List( [ 0 .. n + 1 ], i-> Combinations( [ 0 .. n ], i ) ) );

# For [ 1,2,4] and R it returns the element e1*e2*e4 in R
ring_element := 
    function( l, R )
    if l = [ ] then
        return "1"/R;
    else
        return Product( List( l, i-> Concatenation( "e", String(i) )/R ) );
    fi;
end;

##
DeclareAttribute( "DecompositionOfHomalgMat", IsHomalgMatrix );
InstallMethod( DecompositionOfHomalgMat, 
                 [ IsHomalgMatrix ],
function( d )
local R, n, l, coeff_list, dd, reduction_element, coeff_element, dd_new, u,v, M, m,r;

dd := ShallowCopy( d );

R := d!.ring;

n := Length( IndeterminatesOfExteriorRing( R ) ) -1;

l := standard_list_of_basis_indices( n );

coeff_list := [ ];

for u in l do 

  v := [ 0..n ];
  
  SubtractSet( v, u );
  
  reduction_element := ring_element( v, R );
  
  dd_new := dd*reduction_element;
  
  m := NrColumns( dd_new );
  
  r:= ring_element( Concatenation( u, v ), R );
  
  M := HomalgDiagonalMatrix( List( [ 1 .. m ], i -> r ), R );   
    
  coeff_element := RightDivide( dd_new, M );
 
  Add( coeff_list, [ u, coeff_element ] );
  
  dd := dd - coeff_element*ring_element( u, R );
   
od;

return coeff_list;

end );

##
DeclareGlobalFunction( "FLeft" );
InstallGlobalFunction( FLeft,

function( sigma, A )
local S,n, basis_indices, zero_matrix,d, e_sigma, l;

S := HomalgRing( A );
n := Length( IndeterminatesOfExteriorRing( S ) )-1;
basis_indices := standard_list_of_basis_indices( n );

d := DecompositionOfHomalgMat( A );

zero_matrix := HomalgZeroMatrix( NrRows(A), NrColumns(A), S);

e_sigma := ring_element( sigma, S );

l := List( basis_indices, 
    function( tau )
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
    
    return  ( ( ring_element( lambda, S )* ring_element( tau, S ) )/e_sigma )*d[ m ][ 2 ];
    
    end );
    
return Iterated( l, UnionOfColumns );
    
end );

##
DeclareGlobalFunction( "FRight" );
InstallGlobalFunction( FRight,

function( sigma, A )
local S,n, basis_indices, zero_matrix,d, e_sigma;

S := HomalgRing( A );
n := Length( IndeterminatesOfExteriorRing( S ) )-1;
basis_indices := standard_list_of_basis_indices( n );

d := DecompositionOfHomalgMat( A );

zero_matrix := HomalgZeroMatrix( NrRows( A ), NrColumns( A ), S );

e_sigma := ring_element( sigma, S );

return Iterated( List( basis_indices, 
    function( tau )
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
    
    return  ( ring_element( tau, S )*( ring_element( lambda, S ) )/e_sigma )*d[ m ][ 2 ];
    
    end ), UnionOfRows );
                     
end );
 
DeclareGlobalFunction( "FF2" );
InstallGlobalFunction( FF2,

 function( sigma, A, B )
 
 local R, r,s, AA, BB, Is_Kronecker_AA, BB_Kronecker_Ir; 
 
 R := A!.ring;
 
 r := NrRows( A );
 s := NrColumns( B );
 
 AA := FLeft( sigma, A );
 BB := FRight( sigma, B );
 
 Is_Kronecker_AA :=  KroneckerMat( HomalgIdentityMatrix( s, R ), AA );
 BB_Kronecker_Ir :=  KroneckerMat( Involution( BB ), HomalgIdentityMatrix( r, R ) );
 
 return UnionOfColumns( Is_Kronecker_AA, BB_Kronecker_Ir );
 
 end );


DeclareGlobalFunction( "FF3" );
InstallGlobalFunction( FF3, 

function( A, B )
local S, n, basis_indices;

S := HomalgRing( A );
n := Length( IndeterminatesOfExteriorRing( S ) )-1;
basis_indices := standard_list_of_basis_indices( n );

return UnionOfRows( List( basis_indices, sigma -> FF2( sigma, A, B ) ) );

end );


DeclareGlobalFunction( "SolveTwoSidedEquationOverExteriorAlgebra" );
InstallGlobalFunction( SolveTwoSidedEquationOverExteriorAlgebra,

function( A, B, C )
local C_deco, C_deco_list, C_deco_list_vec, C_vec, N, sol, Q, R, l, m, s, r, n, XX, YY, XX_, YY_, X_, Y_, basis_indices;

if NrRows( A )= 0 or NrColumns( A ) = 0 then 

   return [ "optional", RightDivide( C, B ) ];
   
elif NrRows( B )= 0 or NrColumns( B ) = 0 then 

   return [ LeftDivide( A, C ), "optional" ];
   
fi;

R := HomalgRing( A );

l := Length( IndeterminatesOfExteriorRing( R ) );

basis_indices := standard_list_of_basis_indices( l-1 );

Q := CoefficientsRing( R ); 

C_deco := DecompositionOfHomalgMat( C );

C_deco_list := List( C_deco, i-> i[ 2 ] );

C_deco_list_vec := List( C_deco_list, c-> UnionOfRows( List( [ 1..NrColumns( C ) ], i-> CertainColumns( c, [ i ] ) ) ) );

C_vec := Q*UnionOfRows( C_deco_list_vec );

N := Q*FF3( A, B );

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

X_ := Sum( List( [ 1..2^l ], i-> ( R*CertainRows( XX_, [ ( i - 1 )*m + 1 .. i*m ] ) )* ring_element( basis_indices[ i ], R ) ) );
Y_ := Sum( List( [ 1..2^l ], i-> (R*CertainColumns( YY_, [ ( i - 1 )*n + 1 .. i*n ] ) )* ring_element( basis_indices[ i ], R ) ) );

return [ X_, Y_ ];

end );
