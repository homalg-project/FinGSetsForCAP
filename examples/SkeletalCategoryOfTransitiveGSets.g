#! @Chunk SkeletalCategoryOfTransitiveGSets

#! @Example

LoadPackage( "FinGSetsForCAP", false );
#! true
LoadPackage( "Locales", false );
#! true
S3 := SymmetricGroup( 3 );; StructureDescription( S3 );
#! "S3"
TS3 := SkeletalCategoryOfTransitiveGSets( S3 );
#! SkeletalCategoryOfTransitiveGSets( S3 ) with 4 objects
Display( TS3 );
#! A CAP category with name SkeletalCategoryOfTransitiveGSets( S3 ) \
#! with 4 objects:
#! 
#! 24 primitive operations were used to derive 71 operations for this category \
#! which algorithmically
#! * IsCategoryWithDecidableColifts
#! * IsCategoryWithDecidableLifts
#! * IsCategoryWithTerminalObject
#! * IsFiniteCategory
#! * IsCategoryWithCoequalizers
#! * IsEquippedWithHomomorphismStructure
#! and not yet algorithmically
#! * IsFinitelyPresentedCategory
#! and furthermore mathematically
#! * IsSkeletalCategory
Omega1 := TS3.1;
#! S3 / U_1
Omega2 := TS3.2;
#! S3 / U_2
Omega3 := TS3.3;
#! S3 / U_3
Omega4 := TS3.4;
#! S3 / U_4
objs := SetOfObjects( TS3 );
#! [ S3 / U_1, S3 / U_2, S3 / U_3, S3 / U_4 ]
List( objs, Size );
#! [ 6, 3, 2, 1 ]
t := TerminalObject( TS3 );
#! S3 / U_4
ObjectDatum( t );
#! 4
u := UniversalMorphismIntoTerminalObject( Omega2 );
#! (): S3 / U_2 -> S3 / U_4
MorphismDatum( u );
#! ()
mors := SetOfMorphisms( TS3 );
#! [ (): S3 / U_1 -> S3 / U_1, (2,3): S3 / U_1 -> S3 / U_1,\
#!  (1,2): S3 / U_1 -> S3 / U_1, (1,2,3): S3 / U_1 -> S3 / U_1,\
#!  (1,3,2): S3 / U_1 -> S3 / U_1, (1,3): S3 / U_1 -> S3 / U_1,\
#!  (): S3 / U_1 -> S3 / U_2, (1,3): S3 / U_1 -> S3 / U_2,\
#!  (1,2,3): S3 / U_1 -> S3 / U_2, (): S3 / U_2 -> S3 / U_2,\
#!  (): S3 / U_1 -> S3 / U_3, (2,3): S3 / U_1 -> S3 / U_3,\
#!  (): S3 / U_3 -> S3 / U_3, (2,3): S3 / U_3 -> S3 / U_3,\
#!  (): S3 / U_1 -> S3 / U_4, (): S3 / U_2 -> S3 / U_4,\
#!  (): S3 / U_3 -> S3 / U_4, (): S3 / U_4 -> S3 / U_4 ]
ForAll( mors, IsWellDefined );
#! true
ForAll( mors, IsEpimorphism );
#! true
List( mors, IsEndomorphism );
#! [ true, true, true, true, true, true, false, false, false,\
#!  true, false, false, true, true, false, false, false, true ]
ForAll( mors, mor -> IsMonomorphism( mor ) = IsEndomorphism( mor ) );
#! true
ForAll( mors, mor -> IsSplitMonomorphism( mor ) = IsEndomorphism( mor ) );
#! true
ForAll( mors, mor -> IsSplitEpimorphism( mor ) = IsEndomorphism( mor ) );
#! true
ForAll( mors, mor -> IsIsomorphism( mor ) = IsEndomorphism( mor ) );
#! true
digraph := DigraphOfPoset( PosetOfCategory( TS3 ) );
#! <immutable digraph with 4 vertices, 4 edges>
Print( DotVertexLabelledDigraph( digraph ) );
#! //dot
#! digraph subobject_lattice{
#! rankdir="BT"
#! minlen=0
#! node [shape=circle width=0 height=0 fontsize=12 margin=0.01 \
#! fontname="DejaVu Serif,serif"]
#! edge [arrowsize=0.5]
#! 1 [label="1"]
#! 2 [label="2"]
#! 3 [label="3"]
#! 4 [label="4"]
#! 1 -> 2
#! 1 -> 3
#! 2 -> 4
#! 3 -> 4
#! }
ForAll( objs, o -> o = Coequalizer( Omega1, CoequalizerMorphisms( o ) ) );
#! true

#! @EndExample
