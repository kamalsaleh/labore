

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

DeclareGlobalFunction( "DecomposeHomalgMat" );

InstallGlobalFunction( DecomposeHomalgMat, 

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

  
DeclareGlobalFunction( "RandomRingElement" );

InstallGlobalFunction( RandomRingElement, 

function( R )
local n, l, d, i; 

n := Length( IndeterminatesOfExteriorRing( R ) ) -1;

l := MyList( n );


d := RingElementConstructor( R )( "0", R );                                                          

for i in l do                                     

  d := d + Random( [ -100..100 ] )*RingElement( i, R );

od;

return d;

end );

DeclareGlobalFunction( "RandomHomalgMat" );

InstallGlobalFunction( RandomHomalgMat, 

function( m,n,R ) 

return HomalgMatrix( List( [ 1..m ], i-> List( [ 1..n ], j-> RandomRingElement( R ) ) ), m, n, R ) ;

end );








# R := KoszulDualRing( HomalgFieldOfRationalsInSingular()*"x,y,z,w,t" );
# l := MyList( 4 );
# f := RingElementConstructor( R );                                          





