## test ProjectionOntoCoequalizer

gap> START_TEST( "ProjectionOntoCoequalizer" );

#
gap> LoadPackage( "FinGSetsForCAP", false );
true
gap> S5 := SymmetricGroup( 5 );; StructureDescription( S5 );
"S5"
gap> TS5 := SkeletalCategoryOfTransitiveLeftGSets( S5 );
SkeletalCategoryOfTransitiveLeftGSets( S5 ) with 19 objects
gap> objs := SetOfObjects( TS5 );; Length( objs );
19
gap> Set( objs ) = objs;
true
gap> Omega1 := TS5.1;
S5 / U_1
gap> Omega3 := TS5.3;
S5 / U_3
gap> ForAll( objs, o -> o = CoequalizerOfIdentityAndAutomorphisms( Omega1, List( CoequalizerAutomorphisms( o ), g -> g / TS5 ) ) );
true
gap> mors := SetOfMorphisms( TS5 );; Length( mors );
681
gap> ForAll( mors, IsWellDefined );
true
gap> Y := EmbeddingOfUnderlyingGroupAsCategory( TS5 );
Embedding functor into the skeletal category of transitive left G-sets
gap> I := ExtendFunctorToSkeletalCategoryOfTransitiveLeftGSets( Y );
Extension to SkeletalCategoryOfTransitiveLeftGSets( Source( Embedding functor into\
 the skeletal category of transitive left G-sets ) )
gap> ForAll( mors, mor -> I( mor ) = mor );
true
gap> phi := MorphismConstructor( Omega1, (), Omega3 );
(): S5 / U_1 -> S5 / U_3
gap> psi := MorphismConstructor( Omega1, (1,2,3), Omega3 );
(1,2,3): S5 / U_1 -> S5 / U_3
gap> chi := MorphismConstructor( Omega1, (1,3)(4,5), Omega3 );
(1,3)(4,5): S5 / U_1 -> S5 / U_3
gap> IsWellDefined( phi );
true
gap> IsWellDefined( psi );
true
gap> IsWellDefined( chi );
true
gap> IsCongruentForMorphisms( phi, psi );
false
gap> IsEqualForMorphisms( psi, chi );
false
gap> IsCongruentForMorphisms( psi, chi );
true
gap> IsOne( Colift( phi, psi ) );
false
gap> IsOne( Lift( phi, psi ) );
false
gap> pi := ProjectionOntoCoequalizer( [ phi, psi ] );
(1,3,5,2,4): S5 / U_3 -> S5 / U_11
gap> IsWellDefined( pi );
true
gap> PreCompose( phi, pi ) = PreCompose( psi, pi );
true

#
gap> STOP_TEST( "ProjectionOntoCoequalizer" );
