# SPDX-License-Identifier: GPL-2.0-or-later
# FinGSetsForCAP: The (skeletal) elementary topos of finite G-sets
#
# Declarations
#

#! @Chapter The skeletal category of transitive left G-sets

####################################
#
#! @Section GAP categories
#
####################################

#! @Description
#! The GAP category of the skeletal category of transitive left $G$-sets.
#! @Arguments object
DeclareCategory( "IsCoequalizerCompletionOfGroupAsCategory",
                 IsCapCategory and IsSkeletalCategory );

#! @Description
#! The GAP category of objects in the skeletal category of transitive left $G$-sets.
#! @Arguments object
DeclareCategory( "IsObjectInCoequalizerCompletionOfGroupAsCategory",
                 IsCapCategoryObject );

#! @Description
#! The GAP category of morphisms in the skeletal category of transitive left $G$-sets.
#! @Arguments object
DeclareCategory( "IsMorphismInCoequalizerCompletionOfGroupAsCategory",
                 FilterIntersection( IsCapCategoryMorphism, IsEpimorphism ) );

#! @Description
#! The GAP category of the skeletal category of transitive left $G$-sets.
#! @Arguments object
DeclareCategory( "IsSkeletalCategoryOfTransitiveLeftGSets",
                 IsCapCategory and IsSkeletalCategory );

#! @Description
#! The GAP category of objects in the skeletal category of transitive left $G$-sets.
#! @Arguments object
DeclareCategory( "IsObjectInSkeletalCategoryOfTransitiveLeftGSets",
                 IsCapCategoryObject );

#! @Description
#! The GAP category of morphisms in the skeletal category of transitive left $G$-sets.
#! @Arguments object
DeclareCategory( "IsMorphismInSkeletalCategoryOfTransitiveLeftGSets",
                 FilterIntersection( IsCapCategoryMorphism, IsEpimorphism ) );

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
DeclareAttribute( "CoequalizerCompletion",
                  IsGroupAsCategory );

#! @Description
#! The argument is a group $G$.
#! The output is the skeletal category of transitive $G$-Sets.
#! @Returns a category
#! @Arguments G
DeclareAttribute( "SkeletalCategoryOfTransitiveLeftGSets",
                  IsGroupAsCategory );
#! @InsertChunk SkeletalCategoryOfTransitiveLeftGSets

DeclareAttribute( "SkeletalCategoryOfTransitiveLeftGSets",
                  IsGroup );

####################################
#
#! @Section Attributes
#
####################################

#! @Description
#!  The group $G$ underlying the skeletal category <A>C</A> of transitive left $G$-set.
#! @Arguments C
#! @Returns a group
DeclareAttribute( "UnderlyingGroup",
        IsCoequalizerCompletionOfGroupAsCategory );

CapJitAddTypeSignature( "UnderlyingGroup", [ IsCoequalizerCompletionOfGroupAsCategory ], function ( input_types )
    
    return CapJitDataTypeOfGroup( UnderlyingGroup( input_types[1].category ) );
    
end );

#! @Description
#!  The group $G$ underlying the skeletal category <A>C</A> of transitive left $G$-set, viewed as a category on one object.
#! @Arguments C
#! @Returns a group
DeclareAttribute( "UnderlyingGroupAsCategory",
        IsCoequalizerCompletionOfGroupAsCategory );

CapJitAddTypeSignature( "UnderlyingGroupAsCategory", [ IsCoequalizerCompletionOfGroupAsCategory ], function ( input_types )
    
    return CapJitDataTypeOfCategory( UnderlyingGroupAsCategory( input_types[1].category ) );
    
end );

#! @Description
#!  The table of marks of the group $G$ underlying the skeletal category <A>C</A> of transitive left $G$-set.
#! @Arguments C
#! @Returns a table of marks
DeclareAttribute( "UnderlyingTableOfMarks",
        IsCoequalizerCompletionOfGroupAsCategory );

#! @Description
#!  The number of objects of the skeletal category <A>C</A> of transitive left $G$-set.
#! @Arguments C
#! @Returns a positive integer
DeclareAttribute( "NumberOfObjects",
        IsCoequalizerCompletionOfGroupAsCategory );

CapJitAddTypeSignature( "NumberOfObjects", [ IsCoequalizerCompletionOfGroupAsCategory ], IsBigInt );

#! @Description
#!  The list of cardinalities of objects of the skeletal category <A>C</A> of transitive left $G$-set.
#! @Arguments C
#! @Returns a positive integer
DeclareAttribute( "CardinalitiesOfObjects",
        IsCoequalizerCompletionOfGroupAsCategory );

CapJitAddTypeSignature( "CardinalitiesOfObjects", [ IsCoequalizerCompletionOfGroupAsCategory ], function ( input_types )
    
    return CapJitDataTypeOfListOf( IsBigInt );
    
end );

#! @Description
#!  The list of subgroups up to conjugation of the underlying group.
#! @Arguments C
#! @Returns a positive integer
DeclareAttribute( "RepresentativesOfSubgroupsUpToConjugation",
        IsCoequalizerCompletionOfGroupAsCategory );

CapJitAddTypeSignature( "RepresentativesOfSubgroupsUpToConjugation", [ IsCoequalizerCompletionOfGroupAsCategory ], function ( input_types )
    
    return CapJitDataTypeOfListOf( CapJitDataTypeOfSubgroup( UnderlyingGroup( input_types[1].category ) ) );
    
end );

#! @Description
#!  The positive integer $i$ such that the transitive left $G$-set <A>Omega</A> $\cong U_i \backslash G$.
#! @Arguments Omega
#! @Returns a positive integer
DeclareAttribute( "ObjectNumber",
        IsObjectInCoequalizerCompletionOfGroupAsCategory );

CapJitAddTypeSignature( "ObjectNumber", [ IsObjectInCoequalizerCompletionOfGroupAsCategory ], function ( input_types )
    
    Assert( 0, IsCoequalizerCompletionOfGroupAsCategory( input_types[1].category ) );
    
    return ObjectDatumType( input_types[1].category );
    
end );

#! @Description
#!  The isomorphism defined by the group element $g \in G$ defining the morphism <A>phi</A>: $\cong U_s \backslash G \to U_t \backslash G$
#!  satisfying $g U_s g^{-1} \leq U_t$, or, equivalently, $g U_s \subseteq U_t g$.
#! @Arguments phi
#! @Returns a group element
DeclareAttribute( "UnderlyingIsomorphism",
        IsMorphismInCoequalizerCompletionOfGroupAsCategory );

CapJitAddTypeSignature( "UnderlyingIsomorphism", [ IsMorphismInCoequalizerCompletionOfGroupAsCategory ], function ( input_types )
    
    Assert( 0, IsCoequalizerCompletionOfGroupAsCategory( input_types[1].category ) );
    
    return MorphismDatumType( input_types[1].category );
    
end );

#! @Description
#!  The group $G$ underlying the skeletal category <A>C</A> of transitive left $G$-set.
#! @Arguments C
#! @Returns a group
DeclareAttribute( "UnderlyingGroup",
        IsSkeletalCategoryOfTransitiveLeftGSets );

CapJitAddTypeSignature( "UnderlyingGroup", [ IsSkeletalCategoryOfTransitiveLeftGSets ], function ( input_types )
    
    return CapJitDataTypeOfGroup( UnderlyingGroup( input_types[1].category ) );
    
end );

#! @Description
#!  The group $G$ underlying the skeletal category <A>C</A> of transitive left $G$-set, viewed as a category on one object.
#! @Arguments C
#! @Returns a group
DeclareAttribute( "UnderlyingGroupAsCategory",
        IsSkeletalCategoryOfTransitiveLeftGSets );

#CapJitAddTypeSignature( "UnderlyingGroupAsCategory", [ IsSkeletalCategoryOfTransitiveLeftGSets ], function ( input_types )
#
#    return CapJitDataTypeOfCategory( UnderlyingGroupAsCategory( input_types[1].category ) );
#
#end );

#! @Description
#!  The table of marks of the group $G$ underlying the skeletal category <A>C</A> of transitive left $G$-set.
#! @Arguments C
#! @Returns a table of marks
DeclareAttribute( "UnderlyingTableOfMarks",
        IsSkeletalCategoryOfTransitiveLeftGSets );

#! @Description
#!  The number of objects of the skeletal category <A>C</A> of transitive left $G$-set.
#! @Arguments C
#! @Returns a positive integer
DeclareAttribute( "NumberOfObjects",
        IsSkeletalCategoryOfTransitiveLeftGSets );

CapJitAddTypeSignature( "NumberOfObjects", [ IsSkeletalCategoryOfTransitiveLeftGSets ], IsBigInt );

#! @Description
#!  The list of cardinalities of objects of the skeletal category <A>C</A> of transitive left $G$-set.
#! @Arguments C
#! @Returns a positive integer
DeclareAttribute( "CardinalitiesOfObjects",
        IsSkeletalCategoryOfTransitiveLeftGSets );

CapJitAddTypeSignature( "CardinalitiesOfObjects", [ IsSkeletalCategoryOfTransitiveLeftGSets ], function ( input_types )
    
    return CapJitDataTypeOfListOf( IsBigInt );
    
end );

#! @Description
#!  The list of subgroups up to conjugation of the underlying group.
#! @Arguments C
#! @Returns a positive integer
DeclareAttribute( "RepresentativesOfSubgroupsUpToConjugation",
        IsSkeletalCategoryOfTransitiveLeftGSets );

CapJitAddTypeSignature( "RepresentativesOfSubgroupsUpToConjugation", [ IsSkeletalCategoryOfTransitiveLeftGSets ], function ( input_types )
    
    return CapJitDataTypeOfListOf( CapJitDataTypeOfSubgroup( UnderlyingGroup( input_types[1].category ) ) );
    
end );

#! @Description
#!  The positive integer $i$ such that the transitive left $G$-set <A>Omega</A> $\cong U_i \backslash G$.
#! @Arguments Omega
#! @Returns a positive integer
DeclareAttribute( "ObjectNumber",
        IsObjectInSkeletalCategoryOfTransitiveLeftGSets );

CapJitAddTypeSignature( "ObjectNumber", [ IsObjectInSkeletalCategoryOfTransitiveLeftGSets ], function ( input_types )
    
    Assert( 0, IsSkeletalCategoryOfTransitiveLeftGSets( input_types[1].category ) );
    
    return ObjectDatumType( input_types[1].category );
    
end );

#! @Description
#!  The group elements $g \in G$ defining the morphism <A>phi</A>: $\cong U_s \backslash G \to U_t \backslash G$
#!  satisfying $g U_s g^{-1} \leq U_t$, or, equivalently, $g U_s \subseteq U_t g$.
#! @Arguments phi
#! @Returns a group element
DeclareAttribute( "UnderlyingGroupElement",
        IsMorphismInSkeletalCategoryOfTransitiveLeftGSets );

CapJitAddTypeSignature( "UnderlyingGroupElement", [ IsMorphismInSkeletalCategoryOfTransitiveLeftGSets ], function ( input_types )
    
    Assert( 0, IsSkeletalCategoryOfTransitiveLeftGSets( input_types[1].category ) );
    
    return MorphismDatumType( input_types[1].category );
    
end );

#! @Description
#!  The cardinality of the transitive left $G$-set <A>Omega</A>.
#! @Arguments Omega
#! @Returns a positive integer
DeclareAttribute( "Cardinality",
        IsObjectInSkeletalCategoryOfTransitiveLeftGSets );

#CapJitAddTypeSignature( "Cardinality", [ IsObjectInSkeletalCategoryOfTransitiveLeftGSets ], IsBigInt );

#! @Description
#!  The cardinality of the transitive left $G$-set <A>Omega</A>.
#! @Arguments Omega
#! @Returns a positive integer
DeclareAttribute( "Size",
        IsObjectInSkeletalCategoryOfTransitiveLeftGSets );

#! @Description
#!  The input is a transitive left $G$-set <A>Omega</A> $\cong G / U_i$.
#!  The output is the list of automorphisms of the principal $G$-set $G / U_1$ defined by the generators of $U_i$.
#!  The coequalizers of the identity and these automorphisms is the input object <A>Omega</A> $\cong G / U_i$.
#! @Arguments Omega
#! @Returns a list of morphisms
DeclareAttribute( "CoequalizerAutomorphisms",
        IsObjectInSkeletalCategoryOfTransitiveLeftGSets );

DeclareAttribute( "EmbeddingOfUnderlyingGroupAsCategoryData",
        IsSkeletalCategoryOfTransitiveLeftGSets );

#! @Description
#!  The full embedding functor from the group $G$ underlying
#!  the finite coequalizer completion <A>TG</A> into <A>TG</A>.
#! @Arguments UC
#! @Returns a &CAP; functor
DeclareAttribute( "EmbeddingOfUnderlyingGroupAsCategory",
        IsSkeletalCategoryOfTransitiveLeftGSets );

DeclareOperation( "ExtendFunctorToSkeletalCategoryOfTransitiveLeftGSetsData",
        [ IsSkeletalCategoryOfTransitiveLeftGSets, IsList, IsCategoryWithCoequalizers ] );

#! @Description
#!  The full embedding functor from the group $G$ underlying
#!  the finite coequalizer completion <A>TG</A> into <A>TG</A>.
#! @Arguments UC
#! @Returns a &CAP; functor
DeclareAttribute( "ExtendFunctorToSkeletalCategoryOfTransitiveLeftGSets",
        IsCapFunctor );
