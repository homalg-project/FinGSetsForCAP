# SPDX-License-Identifier: GPL-2.0-or-later
# FinGSetsForCAP: The (skeletal) elementary topos of finite G-sets
#
# Declarations
#

#! @Chapter The skeletal category of transitive G-sets

####################################
#
#! @Section GAP Categories
#
####################################

#! @Description
#! The GAP category of the skeletal category of transitive $G$-sets.
#! @Arguments object
DeclareCategory( "IsSkeletalCategoryOfTransitiveGSets",
                 IsCapCategory and IsSkeletalCategory );

#! @Description
#! The GAP category of objects in the skeletal category of transitive $G$-sets.
#! @Arguments object
DeclareCategory( "IsObjectInSkeletalCategoryOfTransitiveGSets",
                 IsCapCategoryObject );

#! @Description
#! The GAP category of morphisms in the skeletal category of transitive $G$-sets.
#! @Arguments object
DeclareCategory( "IsMorphismInSkeletalCategoryOfTransitiveGSets",
                 IsCapCategoryMorphism );

####################################
#
#! @Section Constructors
#
####################################

#! @Description
#! The argument is a group $G$.
#! The output is the skeletal category of transitive $G$-Sets.
#! @Returns a category
#! @Arguments G
DeclareAttribute( "SkeletalCategoryOfTransitiveGSets",
                  IsGroupAsCategory );
#! @InsertChunk SkeletalCategoryOfTransitiveGSets

DeclareAttribute( "SkeletalCategoryOfTransitiveGSets",
                  IsGroup );

####################################
#
#! @Section Attributes
#
####################################

#! @Description
#!  The group $G$ underlying the skeletal category <A>C</A> of transitive $G$-set.
#! @Arguments C
#! @Returns a group
DeclareAttribute( "UnderlyingGroup",
        IsSkeletalCategoryOfTransitiveGSets );

#CapJitAddTypeSignature( "UnderlyingGroup", [ IsSkeletalCategoryOfTransitiveGSets ], function ( input_types )
#
#    return CapJitDataTypeOfGroup( UnderlyingGroup( input_types[1].category ) );
#
#end );

#! @Description
#!  The group $G$ underlying the skeletal category <A>C</A> of transitive $G$-set, viewed as a category on one object.
#! @Arguments C
#! @Returns a group
DeclareAttribute( "UnderlyingGroupAsCategory",
        IsSkeletalCategoryOfTransitiveGSets );

#CapJitAddTypeSignature( "UnderlyingGroupAsCategory", [ IsSkeletalCategoryOfTransitiveGSets ], function ( input_types )
#
#    return CapJitDataTypeOfCategory( UnderlyingGroupAsCategory( input_types[1].category ) );
#
#end );

#! @Description
#!  The table of marks of the group $G$ underlying the skeletal category <A>C</A> of transitive $G$-set.
#! @Arguments C
#! @Returns a table of marks
DeclareAttribute( "UnderlyingTableOfMarks",
        IsSkeletalCategoryOfTransitiveGSets );

#! @Description
#!  The number of objects of the skeletal category <A>C</A> of transitive $G$-set.
#! @Arguments C
#! @Returns a positive integer
DeclareAttribute( "NumberOfObjects",
        IsSkeletalCategoryOfTransitiveGSets );

CapJitAddTypeSignature( "NumberOfObjects", [ IsSkeletalCategoryOfTransitiveGSets ], IsBigInt );

#! @Description
#!  The list of cardinalities of objects of the skeletal category <A>C</A> of transitive $G$-set.
#! @Arguments C
#! @Returns a positive integer
DeclareAttribute( "CardinalitiesOfObjects",
        IsSkeletalCategoryOfTransitiveGSets );

#CapJitAddTypeSignature( "CardinalitiesOfObjects", [ IsSkeletalCategoryOfTransitiveGSets ], function ( input_types )
#
#    return CapJitDataTypeOfListOf( IsBigInt );
#
#end );

#! @Description
#!  The number of objects of the skeletal category <A>C</A> of transitive $G$-set.
#! @Arguments C
#! @Returns a positive integer
DeclareAttribute( "RepresentativesOfSubgroupsUpToConjugation",
        IsSkeletalCategoryOfTransitiveGSets );

#! @Description
#!  The positive integer $i$ such that the transitive $G$-set <A>Omega</A> $\cong U_i \backslash G$, i.e.,
#!  <C>ObjectNumber( TransitiveGSet( G, i ) ) = i</C>.
#! @Arguments Omega
#! @Returns a positive integer
DeclareAttribute( "ObjectNumber",
        IsObjectInSkeletalCategoryOfTransitiveGSets );

CapJitAddTypeSignature( "ObjectNumber", [ IsObjectInSkeletalCategoryOfTransitiveGSets ], IsBigInt );

#! @Description
#!  The group elements $g \in G$ defining the morphism <A>phi</A>: $\cong U_s \backslash G \to U_t \backslash G$
#!  satisfying $g U_s g^{-1} \leq U_t$, or, equivalently, $g U_s \subseteq U_t g$.
#! @Arguments phi
#! @Returns a group element
DeclareAttribute( "UnderlyingGroupElement",
        IsMorphismInSkeletalCategoryOfTransitiveGSets );

#CapJitAddTypeSignature( "UnderlyingGroupElement", [ IsMorphismInSkeletalCategoryOfTransitiveGSets ], function ( input_types )
#
#    Assert( 0, IsSkeletalCategoryOfTransitiveGSets( input_types[1].category ) );
#
#    return CapJitDataTypeOfElementOfGroup( UnderlyingGroup( input_types[1].category ) );
#
#end );

#! @Description
#!  The cardinality of the transitive $G$-set <A>Omega</A>.
#! @Arguments Omega
#! @Returns a positive integer
DeclareAttribute( "Cardinality",
        IsObjectInSkeletalCategoryOfTransitiveGSets );

CapJitAddTypeSignature( "Cardinality", [ IsObjectInSkeletalCategoryOfTransitiveGSets ], IsBigInt );

#! @Description
#!  The cardinality of the transitive $G$-set <A>Omega</A>.
#! @Arguments Omega
#! @Returns a positive integer
DeclareAttribute( "Size",
        IsObjectInSkeletalCategoryOfTransitiveGSets );

#! @Description
#!  The input is a transitive $G$-set <A>Omega</A> $\cong G / U_i$.
#!  The output is the list of endomorphisms of the principal $G$-set $G / U_1$ defined by the generators of $U_i$.
#!  The coequalizers of these morphisms is the input object <A>Omega</A> $\cong G / U_i$.
#! @Arguments Omega
#! @Returns a list of morphisms
DeclareAttribute( "CoequalizerMorphisms",
        IsObjectInSkeletalCategoryOfTransitiveGSets );

DeclareAttribute( "EmbeddingOfUnderlyingGroupAsCategoryData",
        IsSkeletalCategoryOfTransitiveGSets );

#! @Description
#!  The full embedding functor from the group $G$ underlying
#!  the finite coequalizer completion <A>TG</A> into <A>TG</A>.
#! @Arguments UC
#! @Returns a &CAP; functor
DeclareAttribute( "EmbeddingOfUnderlyingGroupAsCategory",
        IsSkeletalCategoryOfTransitiveGSets );

DeclareOperation( "ExtendFunctorToSkeletalCategoryOfTransitiveGSetsData",
        [ IsSkeletalCategoryOfTransitiveGSets, IsList, IsCategoryWithCoequalizers ] );

#! @Description
#!  The full embedding functor from the group $G$ underlying
#!  the finite coequalizer completion <A>TG</A> into <A>TG</A>.
#! @Arguments UC
#! @Returns a &CAP; functor
DeclareAttribute( "ExtendFunctorToSkeletalCategoryOfTransitiveGSets",
        IsCapFunctor );
