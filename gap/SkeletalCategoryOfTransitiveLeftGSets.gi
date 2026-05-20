# SPDX-License-Identifier: GPL-2.0-or-later
# FinGSetsForCAP: The (skeletal) elementary topos of finite G-sets
#
# Implementations
#

##
InstallMethod( CoequalizerCompletion,
        [ IsGroupAsCategory ],
        
 FunctionWithNamedArguments(
  [
    [ "FinalizeCategory", true ],
    [ "no_precompiled_code", false ],
    [ "overhead", true ],
  ],
  function ( CAP_NAMED_ARGUMENTS, group_as_category )
    local name, category_filter, category_object_filter, category_morphism_filter,
          object_datum_type, morphism_datum_type,
          CoequalizerCompletionOfGroupAsCategory,
          group, name_of_group, tom, u;
    
    name := Concatenation( "CoequalizerCompletion( ", Name( group_as_category ), " )" );
    
    ##
    category_filter := IsCoequalizerCompletionOfGroupAsCategory;
    category_object_filter := IsObjectInCoequalizerCompletionOfGroupAsCategory;
    category_morphism_filter := IsMorphismInCoequalizerCompletionOfGroupAsCategory;
    
    ##
    object_datum_type := IsBigInt;
    
    ##
    morphism_datum_type := CapJitDataTypeOfMorphismOfCategory( group_as_category );
    
    CoequalizerCompletionOfGroupAsCategory :=
      CreateCapCategoryWithDataTypes(
              name,
              category_filter,
              category_object_filter,
              category_morphism_filter,
              IsCapCategoryTwoCell,
              object_datum_type,
              morphism_datum_type,
              fail :
              overhead := CAP_NAMED_ARGUMENTS.overhead );
    
    group := UnderlyingGroup( group_as_category );
    
    if HasName( group ) then
        # COVERAGE_IGNORE_NEXT_LINE
        name_of_group := Name( group );
    elif HasStructureDescription( group ) then
        name_of_group := StructureDescription( group );
    else
        # COVERAGE_IGNORE_NEXT_LINE
        name_of_group := String( group );
    fi;
    
    tom := TableOfMarks( group );
    u := Length( MarksTom( tom ) );
    
    CoequalizerCompletionOfGroupAsCategory!.name_of_group := name_of_group;
    
    CoequalizerCompletionOfGroupAsCategory!.category_as_first_argument := true;
    CoequalizerCompletionOfGroupAsCategory!.supports_empty_limits := true;
    
    SetUnderlyingGroup( CoequalizerCompletionOfGroupAsCategory, group );
    SetUnderlyingGroupAsCategory( CoequalizerCompletionOfGroupAsCategory, group_as_category );
    SetUnderlyingTableOfMarks( CoequalizerCompletionOfGroupAsCategory, tom );
    SetNumberOfObjects( CoequalizerCompletionOfGroupAsCategory, u );
    SetCardinalitiesOfObjects( CoequalizerCompletionOfGroupAsCategory, List( MarksTom( tom ), beta -> beta[1] ) );
    SetRepresentativesOfSubgroupsUpToConjugation( CoequalizerCompletionOfGroupAsCategory, List( [ 1 .. u ], i -> RepresentativeTom( tom, i ) ) );
    
    CoequalizerCompletionOfGroupAsCategory!.compiler_hints :=
      rec( category_attribute_names :=
           [ "UnderlyingGroup",
             "UnderlyingGroupAsCategory",
             "UnderlyingTableOfMarks",
             "NumberOfObjects",
             "CardinalitiesOfObjects",
             "RepresentativesOfSubgroupsUpToConjugation",
             ] );
    
    # this is a workhorse category -> no logic and caching only via IsIdenticalObj
    CapCategorySwitchLogicOff( CoequalizerCompletionOfGroupAsCategory );
    
    SetIsFiniteCategory( CoequalizerCompletionOfGroupAsCategory, true );
    SetIsCategoryWithDecidableLifts( CoequalizerCompletionOfGroupAsCategory, true );
    SetIsCategoryWithDecidableColifts( CoequalizerCompletionOfGroupAsCategory, true );
    SetIsCategoryWithCoequalizers( CoequalizerCompletionOfGroupAsCategory, true );
    SetIsCategoryWithTerminalObject( CoequalizerCompletionOfGroupAsCategory, true );
    SetIsSkeletalCategory( CoequalizerCompletionOfGroupAsCategory, true );
    
    SetIsEquippedWithHomomorphismStructure( CoequalizerCompletionOfGroupAsCategory, true );
    SetRangeCategoryOfHomomorphismStructure( CoequalizerCompletionOfGroupAsCategory, SkeletalFinSets );
    
    ##
    AddObjectConstructor( CoequalizerCompletionOfGroupAsCategory,
      function ( CoequalizerCompletionOfGroupAsCategory, i )
        
        #% CAP_JIT_DROP_NEXT_STATEMENT
        if not i in [ 1 .. NumberOfObjects( CoequalizerCompletionOfGroupAsCategory ) ] then
            # COVERAGE_IGNORE_NEXT_LINE
            return Error( "i must be an integer in the interval ", [ 1 .. NumberOfObjects( CoequalizerCompletionOfGroupAsCategory ) ] );
        fi;
        
        return CreateCapCategoryObjectWithAttributes( CoequalizerCompletionOfGroupAsCategory,
                       ObjectNumber, i );
        
    end );
    
    ##
    AddObjectDatum( CoequalizerCompletionOfGroupAsCategory,
      function ( CoequalizerCompletionOfGroupAsCategory, Omega )
        
        return ObjectNumber( Omega );
        
    end );
    
    ##
    AddMorphismConstructor( CoequalizerCompletionOfGroupAsCategory,
      function ( CoequalizerCompletionOfGroupAsCategory, source, g, target )
        
        ## a morphism G/U → G/V is uniquely determined by the image of the standard left coset
        ## G/U → G/V, U ↦ g V, and by equivariance ∀ h ∈ U, h U ↦ h g V
        ## see the comments for AddIsWellDefinedForMorphisms below
        return CreateCapCategoryMorphismWithAttributes( CoequalizerCompletionOfGroupAsCategory,
                       source,
                       target,
                       UnderlyingIsomorphism, g );
        
    end );
    
    ##
    AddMorphismDatum( CoequalizerCompletionOfGroupAsCategory,
      function ( CoequalizerCompletionOfGroupAsCategory, phi )
        
        return UnderlyingIsomorphism( phi );
        
    end );
    
    ##
    AddSetOfObjectsOfCategory( CoequalizerCompletionOfGroupAsCategory,
      function ( CoequalizerCompletionOfGroupAsCategory )
        
        return List( [ 1 .. NumberOfObjects( CoequalizerCompletionOfGroupAsCategory ) ], i -> ObjectConstructor( CoequalizerCompletionOfGroupAsCategory, i ) );
        
    end );
    
    ##
    AddIsWellDefinedForObjects( CoequalizerCompletionOfGroupAsCategory,
      function ( CoequalizerCompletionOfGroupAsCategory, Omega )
        
        return ObjectNumber( Omega ) in [ 1 .. NumberOfObjects( CoequalizerCompletionOfGroupAsCategory ) ];
        
    end );
    
    ##
    AddIsWellDefinedForMorphisms( CoequalizerCompletionOfGroupAsCategory,
      function ( CoequalizerCompletionOfGroupAsCategory, phi )
        local U, s, t, g;
        
        U := RepresentativesOfSubgroupsUpToConjugation( CoequalizerCompletionOfGroupAsCategory );
        
        s := ObjectNumber( Source( phi ) );
        t := ObjectNumber( Target( phi ) );
        
        ## a morphism G/U[s] → G/U[t] is uniquely determined by the image of the standard left coset
        ## G/U[s] → G/U[t], U[s] ↦ g U[t], and by equivariance ∀ h ∈ U, h U[s] ↦ h g U[t]
        g := UnderlyingGroupElement( UnderlyingIsomorphism( phi ) );
        
        return g in UnderlyingGroup( CoequalizerCompletionOfGroupAsCategory ) and
               ## well-defined means equal input results in equal output:
               ## U[s] = h U[s] ⟹ g U[t] = h g U[t] (by equivariance) ⟺
               ## ∀ h ∈ U[s], g⁻¹ h g ∈ U[t] ⟺ g⁻¹ U[s] g ≕ U[s]ᵍ ⊆ U[t]
               IsSubset( U[t], ConjugateSubgroup( U[s], g ) ); ## ConjugateSubgroup( U[s], g ) ≔ g⁻¹ U[s] g ≕ U[s]ᵍ ⊆ U[t]
        
    end );
    
    ##
    AddIsEqualForObjects( CoequalizerCompletionOfGroupAsCategory,
      function ( CoequalizerCompletionOfGroupAsCategory, Omega1, Omega2 )
        
        return ObjectNumber( Omega1 ) = ObjectNumber( Omega2 );
        
    end );
    
    ##
    AddIsEqualForMorphisms( CoequalizerCompletionOfGroupAsCategory,
      function ( CoequalizerCompletionOfGroupAsCategory, phi, psi )
        local group_as_category;
        
        group_as_category := UnderlyingGroupAsCategory( CoequalizerCompletionOfGroupAsCategory );
        
        return IsEqualForMorphisms( group_as_category,
                       UnderlyingIsomorphism( phi ),
                       UnderlyingIsomorphism( psi ) );
        
    end );
    
    ##
    AddIsCongruentForMorphisms( CoequalizerCompletionOfGroupAsCategory,
      function ( CoequalizerCompletionOfGroupAsCategory, phi, psi )
        local group_as_category, U, t, gi_h;
        
        group_as_category := UnderlyingGroupAsCategory( CoequalizerCompletionOfGroupAsCategory );
        
        U := RepresentativesOfSubgroupsUpToConjugation( CoequalizerCompletionOfGroupAsCategory );
        
        t := ObjectNumber( Target( phi ) );
        
        ## two parallel morphisms uniquely determined by their images of the standard left coset
        ## phi: G/U[s] → G/U[t], U[s] ↦ g U[t], psi: G/U[s] → G/U[t], U[s] ↦ h U[t]
        ## are equal, iff their image cosets are equal:
        ## g U[t] = h U[t] ⟺ U[t] = g⁻¹ h U[t] ⟺ g⁻¹ h ∈ U[t]
        gi_h := PreCompose( group_as_category,
                        InverseForMorphisms( group_as_category, UnderlyingIsomorphism( phi ) ),
                        UnderlyingIsomorphism( psi ) );
        
        return UnderlyingGroupElement( gi_h ) in U[t];
        
    end );
    
    ##
    AddIdentityMorphism( CoequalizerCompletionOfGroupAsCategory,
      function ( CoequalizerCompletionOfGroupAsCategory, Omega )
        local group_as_category;
        
        group_as_category := UnderlyingGroupAsCategory( CoequalizerCompletionOfGroupAsCategory );
        
        return MorphismConstructor( CoequalizerCompletionOfGroupAsCategory,
                       Omega,
                       IdentityMorphism( group_as_category, GroupAsCategoryUniqueObject( group_as_category ) ),
                       Omega );
        
    end );
    
    ##
    AddPreCompose( CoequalizerCompletionOfGroupAsCategory,
      function ( CoequalizerCompletionOfGroupAsCategory, mor_pre, mor_post )
        local group_as_category;
        
        group_as_category := UnderlyingGroupAsCategory( CoequalizerCompletionOfGroupAsCategory );
        
        ## we choose the left cosets in order for the embedding G ↪ SkeletalCategoryOfTransitiveLeftGSets( G ) to be covariant:
        ## g: G/U → G/V, h: G/V → G/W, translates to Uᵍ ⊆ V, Vʰ ⊆ W ⟹ Uᵍʰ ⊆ Vʰ ⊆ W
        return MorphismConstructor( CoequalizerCompletionOfGroupAsCategory,
                       Source( mor_pre ),
                       PreCompose( group_as_category, UnderlyingIsomorphism( mor_pre ), UnderlyingIsomorphism( mor_post ) ),
                       Target( mor_post ) );
        
    end );
    
    ##
    AddIsLiftable( CoequalizerCompletionOfGroupAsCategory,
      function ( CoequalizerCompletionOfGroupAsCategory, alpha, beta )
        local group_as_category, U, s, t, g;
        
        group_as_category := UnderlyingGroupAsCategory( CoequalizerCompletionOfGroupAsCategory );
        
        U := RepresentativesOfSubgroupsUpToConjugation( CoequalizerCompletionOfGroupAsCategory );
        
        s := ObjectNumber( Source( alpha ) );
        t := ObjectNumber( Source( beta ) );
        
        g := UnderlyingGroupElement( Lift( group_as_category, UnderlyingIsomorphism( alpha ), UnderlyingIsomorphism( beta ) ) );
        
        return IsSubset( U[t], ConjugateSubgroup( U[s], g ) );
        
    end );
    
    ##
    AddLift( CoequalizerCompletionOfGroupAsCategory,
      function ( CoequalizerCompletionOfGroupAsCategory, alpha, beta )
        local group_as_category;
        
        group_as_category := UnderlyingGroupAsCategory( CoequalizerCompletionOfGroupAsCategory );
        
        return MorphismConstructor( CoequalizerCompletionOfGroupAsCategory,
                       Source( alpha ),
                       Lift( group_as_category, UnderlyingIsomorphism( alpha ), UnderlyingIsomorphism( beta ) ),
                       Source( beta ) );
        
    end );
    
    ##
    AddIsColiftable( CoequalizerCompletionOfGroupAsCategory,
      function ( CoequalizerCompletionOfGroupAsCategory, alpha, beta )
        local group_as_category, U, s, t, g;
        
        group_as_category := UnderlyingGroupAsCategory( CoequalizerCompletionOfGroupAsCategory );
        
        U := RepresentativesOfSubgroupsUpToConjugation( CoequalizerCompletionOfGroupAsCategory );
        
        s := ObjectNumber( Target( alpha ) );
        t := ObjectNumber( Target( beta ) );
        
        g := UnderlyingGroupElement( Colift( group_as_category, UnderlyingIsomorphism( alpha ), UnderlyingIsomorphism( beta ) ) );
        
        return IsSubset( U[t], ConjugateSubgroup( U[s], g ) );
        
    end );
    
    ##
    AddColift( CoequalizerCompletionOfGroupAsCategory,
      function ( CoequalizerCompletionOfGroupAsCategory, alpha, beta )
        local group_as_category;
        
        group_as_category := UnderlyingGroupAsCategory( CoequalizerCompletionOfGroupAsCategory );
        
        return MorphismConstructor( CoequalizerCompletionOfGroupAsCategory,
                       Target( alpha ),
                       Colift( group_as_category, UnderlyingIsomorphism( alpha ), UnderlyingIsomorphism( beta ) ),
                       Target( beta ) );
        
    end );
    
    ##
    AddTerminalObject( CoequalizerCompletionOfGroupAsCategory,
      function ( CoequalizerCompletionOfGroupAsCategory )
        
        return ObjectConstructor( CoequalizerCompletionOfGroupAsCategory, NumberOfObjects( CoequalizerCompletionOfGroupAsCategory ) );
        
    end );
    
    ##
    AddUniversalMorphismIntoTerminalObjectWithGivenTerminalObject( CoequalizerCompletionOfGroupAsCategory,
      function ( CoequalizerCompletionOfGroupAsCategory, Omega, trivial_G_set )
        local group_as_category;
        
        group_as_category := UnderlyingGroupAsCategory( CoequalizerCompletionOfGroupAsCategory );
        
        return MorphismConstructor( CoequalizerCompletionOfGroupAsCategory,
                       Omega,
                       IdentityMorphism( group_as_category, GroupAsCategoryUniqueObject( group_as_category ) ),
                       trivial_G_set );
        
    end );
    
    ## for two parallel morphisms uniquely determined by their images of the standard left coset
    ## φ: G/U[s] → G/U[t], U[s] ↦ a U[t], ψ: G/U[s] → G/U[t], U[s] ↦ b U[t],
    ## the projection onto the coequalizer is given by a morphism π: G/U[t] → G/U[c], U[t] ↦ g U[c],
    ## which has to satisfy U[t]ᵍ ⊆ U[c] and (a g) U[c] = (b g) U[c] ⟺ g⁻¹ a⁻¹ b g ∈ U[c],
    ## which simplify to ⟨ U[t], a⁻¹ b ⟩ᵍ ⊆ U[c], and hence ⟨ U[t], a⁻¹ b ⟩ᵍ = U[c].
    AddProjectionOntoCoequalizer( CoequalizerCompletionOfGroupAsCategory,
      function ( CoequalizerCompletionOfGroupAsCategory, target, diagram )
        local group_as_category, G, U, objects, t, l, gs, C, Ucoeq, index, cards, positions, pos, g, coeq;
        
        group_as_category := UnderlyingGroupAsCategory( CoequalizerCompletionOfGroupAsCategory );
        
        G := UnderlyingGroup( CoequalizerCompletionOfGroupAsCategory );
        
        U := RepresentativesOfSubgroupsUpToConjugation( CoequalizerCompletionOfGroupAsCategory );
        
        objects := SetOfObjects( CoequalizerCompletionOfGroupAsCategory );
        
        t := ObjectNumber( target );
        
        l := Length( diagram );
        
        gs := List( [ 1 .. l ], i -> UnderlyingIsomorphism( diagram[i] ) );
        
        C := List( [ 1 .. l - 1 ], i -> UnderlyingGroupElement( Colift( group_as_category, gs[i], gs[i + 1] ) ) );
        
        Ucoeq := Subgroup( G, Concatenation( GeneratorsOfGroup( U[t] ), C ) );
        
        index := Index( G, Ucoeq );
        
        cards := CardinalitiesOfObjects( CoequalizerCompletionOfGroupAsCategory );
        
        positions := Filtered( [ 1 .. NumberOfObjects( CoequalizerCompletionOfGroupAsCategory ) ], i -> cards[i] = index );
        
        ## pos := SafeUniqueEntry( positions, c -> IsConjugate( G, Ucoeq, U[c] ) );
        ## but for performance we use:
        pos := SafeFirst( positions, c -> IsConjugate( G, Ucoeq, U[c] ) );
        
        g := RepresentativeAction( G, Ucoeq, U[pos] );
        
        coeq := objects[pos];
        
        return MorphismConstructor( CoequalizerCompletionOfGroupAsCategory,
                       target,
                       GroupAsCategoryMorphism( group_as_category, g ),
                       coeq );
    end );
    
    ##
    AddProjectionOntoCoequalizerOfIdentityAndAutomorphisms( CoequalizerCompletionOfGroupAsCategory,
      function ( CoequalizerCompletionOfGroupAsCategory, target, automorphisms )
        local group_as_category, G, U, objects, t, gs, Ucoeq, index, cards, positions, pos, g, coeq;
        
        group_as_category := UnderlyingGroupAsCategory( CoequalizerCompletionOfGroupAsCategory );
        
        G := UnderlyingGroup( CoequalizerCompletionOfGroupAsCategory );
        
        U := RepresentativesOfSubgroupsUpToConjugation( CoequalizerCompletionOfGroupAsCategory );
        
        objects := SetOfObjects( CoequalizerCompletionOfGroupAsCategory );
        
        t := ObjectNumber( target );
        
        gs := List( [ 1 .. Length( automorphisms ) ], i ->
                    UnderlyingGroupElement( UnderlyingIsomorphism( automorphisms[i] ) ) );
        
        Ucoeq := Subgroup( G, Concatenation( GeneratorsOfGroup( U[t] ), gs ) );
        
        index := Index( G, Ucoeq );
        
        cards := CardinalitiesOfObjects( CoequalizerCompletionOfGroupAsCategory );
        
        positions := Filtered( [ 1 .. NumberOfObjects( CoequalizerCompletionOfGroupAsCategory ) ], i -> cards[i] = index );
        
        ## pos := SafeUniqueEntry( positions, c -> IsConjugate( G, Ucoeq, U[c] ) );
        ## but for performance we use:
        pos := SafeFirst( positions, c -> IsConjugate( G, Ucoeq, U[c] ) );
        
        g := RepresentativeAction( G, Ucoeq, U[pos] );
        
        coeq := objects[pos];
        
        return MorphismConstructor( CoequalizerCompletionOfGroupAsCategory,
                       target,
                       GroupAsCategoryMorphism( group_as_category, g ),
                       coeq );
        
    end );
    
    ##
    AddIsHomSetInhabited( CoequalizerCompletionOfGroupAsCategory,
      function ( CoequalizerCompletionOfGroupAsCategory, source, target )
        local G, U, s, t, L;
        
        G := UnderlyingGroup( CoequalizerCompletionOfGroupAsCategory );
        
        U := RepresentativesOfSubgroupsUpToConjugation( CoequalizerCompletionOfGroupAsCategory );
        
        s := ObjectNumber( source );
        t := ObjectNumber( target );
        
        ## LeftTransversal is not defined in GAP
        L := List( RightTransversal( G, U[t] ), Inverse );
        
        return ForAny( L, g -> IsSubset( ConjugateSubgroup( U[t], Inverse( g ) ), U[s] ) );
        
    end );
    
    ##
    AddMorphismsOfExternalHom( CoequalizerCompletionOfGroupAsCategory,
      function ( CoequalizerCompletionOfGroupAsCategory, source, target )
        local group_as_category, G, U, s, t, L;
        
        group_as_category := UnderlyingGroupAsCategory( CoequalizerCompletionOfGroupAsCategory );
        
        G := UnderlyingGroup( CoequalizerCompletionOfGroupAsCategory );
        
        U := RepresentativesOfSubgroupsUpToConjugation( CoequalizerCompletionOfGroupAsCategory );
        
        s := ObjectNumber( source );
        t := ObjectNumber( target );
        
        ## LeftTransversal is not defined in GAP
        L := List( RightTransversal( G, U[t] ), Inverse );
        
        L := Filtered( L, g -> IsSubset( U[t], ConjugateSubgroup( U[s], g ) ) );
        
        return List( L, g ->
                     MorphismConstructor( CoequalizerCompletionOfGroupAsCategory,
                             source,
                             GroupAsCategoryMorphism( group_as_category, g ),
                             target ) );
        
    end );
    
    ##
    AddIsEpimorphism( CoequalizerCompletionOfGroupAsCategory,
      function ( CoequalizerCompletionOfGroupAsCategory, phi )
        
        return true;
        
    end );
    
    ##
    AddIsMonomorphism( CoequalizerCompletionOfGroupAsCategory,
      function ( CoequalizerCompletionOfGroupAsCategory, phi )
        
        return IsEndomorphism( CoequalizerCompletionOfGroupAsCategory, phi );
        
    end );
    
    ##
    AddIsIsomorphism( CoequalizerCompletionOfGroupAsCategory,
      function ( CoequalizerCompletionOfGroupAsCategory, phi )
        
        return IsMonomorphism( CoequalizerCompletionOfGroupAsCategory, phi );
        
    end );
    
    if CAP_NAMED_ARGUMENTS.FinalizeCategory then
        Finalize( CoequalizerCompletionOfGroupAsCategory );
    fi;
    
    return CoequalizerCompletionOfGroupAsCategory;
    
end ) );

##
InstallMethod( SkeletalCategoryOfTransitiveLeftGSets,
        [ IsGroupAsCategory ],
        
 FunctionWithNamedArguments(
  [
    [ "FinalizeCategory", true ],
    [ "no_precompiled_code", false ],
    [ "overhead", true ],
  ],
  function ( CAP_NAMED_ARGUMENTS, group_as_category )
    local group,
          category_filter, category_object_filter, category_morphism_filter,
          object_datum_type, object_constructor, object_datum,
          morphism_datum_type, morphism_constructor, morphism_datum,
          CoequalizerCompletionOfGroupAsCategory,
          modeling_tower_object_constructor, modeling_tower_object_datum,
          modeling_tower_morphism_constructor, modeling_tower_morphism_datum,
          name_of_group, u,
          name, SkeletalTransitiveLeftGSets;

    group := UnderlyingGroup( group_as_category );
    
    ##
    category_filter := IsSkeletalCategoryOfTransitiveLeftGSets;
    category_object_filter := IsObjectInSkeletalCategoryOfTransitiveLeftGSets;
    category_morphism_filter := IsMorphismInSkeletalCategoryOfTransitiveLeftGSets;
    
    ##
    object_datum_type := IsBigInt;
    
    ##
    object_constructor :=
      function ( SkeletalTransitiveLeftGSets, object_number )
        
        return CreateCapCategoryObjectWithAttributes( SkeletalTransitiveLeftGSets,
                       ObjectNumber, object_number );
        
    end;
    
    ##
    object_datum :=
      function ( SkeletalTransitiveLeftGSets, Omega )
        
        return ObjectNumber( Omega );
        
    end;
    
    ##
    morphism_datum_type := CapJitDataTypeOfElementOfGroup( group );
    
    ##
    morphism_constructor :=
      function ( SkeletalTransitiveLeftGSets, S, g, T )
        
        return CreateCapCategoryMorphismWithAttributes( SkeletalTransitiveLeftGSets,
                       S,
                       T,
                       UnderlyingGroupElement, g );
        
    end;
    
    ##
    morphism_datum :=
      function ( SkeletalTransitiveLeftGSets, phi )
        
        return UnderlyingGroupElement( phi );
        
    end;
    
    ## building the categorical tower:
    
    CoequalizerCompletionOfGroupAsCategory := CoequalizerCompletion( group_as_category : FinalizeCategory := true );
    
    ## from the raw object data to the object in the modeling category
    modeling_tower_object_constructor :=
      function ( SkeletalTransitiveLeftGSets, object_number )
        local CoequalizerCompletionOfGroupAsCategory;
        
        CoequalizerCompletionOfGroupAsCategory := ModelingCategory( SkeletalTransitiveLeftGSets );
        
        return ObjectConstructor( CoequalizerCompletionOfGroupAsCategory, object_number );
        
    end;
    
    ## from the object in the modeling category to the raw object data
    modeling_tower_object_datum :=
      function ( SkeletalTransitiveLeftGSets, Omega )
        
        return ObjectNumber( Omega );
        
    end;
    
    ## from the raw morphism data to the morphism in the modeling category
    modeling_tower_morphism_constructor :=
      function ( SkeletalTransitiveLeftGSets, source, g, target )
        local CoequalizerCompletionOfGroupAsCategory, group_as_category;
        
        CoequalizerCompletionOfGroupAsCategory := ModelingCategory( SkeletalTransitiveLeftGSets );
        
        group_as_category := UnderlyingGroupAsCategory( CoequalizerCompletionOfGroupAsCategory );
        
        return MorphismConstructor( CoequalizerCompletionOfGroupAsCategory,
                       source,
                       GroupAsCategoryMorphism( group_as_category, g ),
                       target );
        
    end;
    
    ## from the morphism in the modeling category to the raw morphism data
    modeling_tower_morphism_datum :=
      function ( SkeletalTransitiveLeftGSets, phi )
        
        return UnderlyingGroupElement( UnderlyingIsomorphism( phi ) );
        
    end;
    
    name_of_group := CoequalizerCompletionOfGroupAsCategory!.name_of_group;
    
    u := NumberOfObjects( CoequalizerCompletionOfGroupAsCategory );
    
    name := Concatenation( "SkeletalCategoryOfTransitiveLeftGSets( ", name_of_group, " ) with ", String( u ), " objects" );
    
    ##
    SkeletalTransitiveLeftGSets :=
      ReinterpretationOfCategory( CoequalizerCompletionOfGroupAsCategory,
              rec( name := name,
                   category_filter := category_filter,
                   category_object_filter := category_object_filter,
                   category_morphism_filter := category_morphism_filter,
                   object_datum_type := object_datum_type,
                   morphism_datum_type := morphism_datum_type,
                   object_constructor := object_constructor,
                   object_datum := object_datum,
                   morphism_constructor := morphism_constructor,
                   morphism_datum := morphism_datum,
                   modeling_tower_object_constructor := modeling_tower_object_constructor,
                   modeling_tower_object_datum := modeling_tower_object_datum,
                   modeling_tower_morphism_constructor := modeling_tower_morphism_constructor,
                   modeling_tower_morphism_datum := modeling_tower_morphism_datum,
                   only_primitive_operations := true )
              : FinalizeCategory := false );
    
    SkeletalTransitiveLeftGSets!.name_of_group := name_of_group;
    
    SetUnderlyingGroup( SkeletalTransitiveLeftGSets, group );
    SetUnderlyingGroupAsCategory( SkeletalTransitiveLeftGSets, group_as_category );
    SetUnderlyingTableOfMarks( SkeletalTransitiveLeftGSets, UnderlyingTableOfMarks( CoequalizerCompletionOfGroupAsCategory ) );
    SetNumberOfObjects( SkeletalTransitiveLeftGSets, u );
    SetCardinalitiesOfObjects( SkeletalTransitiveLeftGSets, CardinalitiesOfObjects( CoequalizerCompletionOfGroupAsCategory ) );
    SetRepresentativesOfSubgroupsUpToConjugation( SkeletalTransitiveLeftGSets, RepresentativesOfSubgroupsUpToConjugation( CoequalizerCompletionOfGroupAsCategory ) );
    
    Append( SkeletalTransitiveLeftGSets!.compiler_hints.category_attribute_names,
            [ "UnderlyingGroup",
              "UnderlyingGroupAsCategory",
              "UnderlyingTableOfMarks",
              "NumberOfObjects",
              "CardinalitiesOfObjects",
              "SetOfObjectsAsUnresolvableAttribute",
              "RepresentativesOfSubgroupsUpToConjugation",
              ] );
    
    # this is a workhorse category -> no logic and caching only via IsIdenticalObj
    CapCategorySwitchLogicOff( SkeletalTransitiveLeftGSets );
    
    if CAP_NAMED_ARGUMENTS.no_precompiled_code <> true then
        
        ADD_FUNCTIONS_FOR_SkeletalCategoryOfTransitiveLeftGSets_precompiled( SkeletalTransitiveLeftGSets );
        
    fi;
    
    if CAP_NAMED_ARGUMENTS.FinalizeCategory then
        Finalize( SkeletalTransitiveLeftGSets );
    fi;
    
    return SkeletalTransitiveLeftGSets;
    
end ) );

##
InstallMethod( SkeletalCategoryOfTransitiveLeftGSets,
        [ IsGroup ],
        
  function ( G )
    
    return SkeletalCategoryOfTransitiveLeftGSets( GroupAsCategory( G ) );
    
end );

##
InstallMethod( \<,
        "for two skeletal transitive left G-sets",
        [ IsObjectInSkeletalCategoryOfTransitiveLeftGSets, IsObjectInSkeletalCategoryOfTransitiveLeftGSets ],
        
  function ( Omega1, Omega2 )
    
    return ObjectNumber( Omega1 ) < ObjectNumber( Omega2 );
    
end );

##
InstallMethod( \.,
        "for the skeletal category of transitive left G-sets and a positive integer",
        [ IsSkeletalCategoryOfTransitiveLeftGSets, IsPosInt ],

  function ( SkeletalTransitiveLeftGSets, string_as_int )
    local name;
    
    name := NameRNam( string_as_int );
    
    return EvalString( name ) / SkeletalTransitiveLeftGSets;
    
end );

##
InstallMethodForCompilerForCAP( SetOfObjects,
        "for the coequalizer completion of a group as category",
        [ IsCoequalizerCompletionOfGroupAsCategory ],
        
  function ( CoequalizerCompletionOfGroupAsCategory )
    
    return SetOfObjectsOfCategory( CoequalizerCompletionOfGroupAsCategory );
    
end );

##
InstallMethodForCompilerForCAP( SetOfObjects,
        "for the skeletal category of transitive left G-sets",
        [ IsSkeletalCategoryOfTransitiveLeftGSets ],
        
  function ( SkeletalTransitiveLeftGSets )
    
    return SetOfObjectsAsUnresolvableAttribute( SkeletalTransitiveLeftGSets );
    
end );

##
InstallMethod( \/,
        "for a morphism in the underlying group as category and the skeletal category of transitive G-sets",
        [ IsMorphismInGroupAsCategory, IsSkeletalCategoryOfTransitiveLeftGSets ],
        
  function ( g, TG )
    local P, auto;
    
    P := TG.1;
    
    auto := MorphismConstructor( TG,
                    P,
                    UnderlyingGroupElement( g ),
                    P );
    
    SetIsIsomorphism( auto, true );
    
    return auto;
    
end );

##
InstallMethod( Cardinality,
        "for a skeletal transitive left G-set",
        [ IsObjectInSkeletalCategoryOfTransitiveLeftGSets ],
        
  function ( Omega )
    local SkeletalTransitiveLeftGSets, U;
    
    SkeletalTransitiveLeftGSets := CapCategory( Omega );
    
    U := RepresentativesOfSubgroupsUpToConjugation( SkeletalTransitiveLeftGSets );
    
    return Index( UnderlyingGroup( SkeletalTransitiveLeftGSets ), U[ObjectNumber( Omega )] );
    
end );

##
InstallMethod( Size,
        "for a skeletal transitive left G-set",
        [ IsObjectInSkeletalCategoryOfTransitiveLeftGSets ],
        
  function ( Omega )
    
    return Cardinality( Omega );
    
end );

##
InstallOtherMethodForCompilerForCAP( CoequalizerAutomorphisms,
        "for the skeletal category of transitive left G-sets and a transitive left G-set therein",
        [ IsSkeletalCategoryOfTransitiveLeftGSets, IsObjectInSkeletalCategoryOfTransitiveLeftGSets ],
        
  function ( SkeletalTransitiveLeftGSets, Omega )
    local G_as_cat, P, U, gs;

    G_as_cat := UnderlyingGroupAsCategory( SkeletalTransitiveLeftGSets );
    
    P := GroupAsCategoryUniqueObject( G_as_cat );
    
    U := RepresentativesOfSubgroupsUpToConjugation( SkeletalTransitiveLeftGSets );
    
    gs := GeneratorsOfGroup( U[ObjectNumber( Omega )] );
    
    return List( gs, g ->
                 MorphismConstructor( G_as_cat,
                         P,
                         g,
                         P ) );
    
end );

##
InstallMethod( CoequalizerAutomorphisms,
        "for a skeletal transitive left G-set",
        [ IsObjectInSkeletalCategoryOfTransitiveLeftGSets ],
        
  function ( Omega )
    
    return CoequalizerAutomorphisms( CapCategory( Omega ), Omega );
    
end );

##
InstallMethodForCompilerForCAP( EmbeddingOfUnderlyingGroupAsCategoryData,
        "for a skeletal category of transitive left G-sets",
        [ IsSkeletalCategoryOfTransitiveLeftGSets ],
        
  function ( SkeletalTransitiveLeftGSets )
    local embedding_on_objects, embedding_on_morphisms;
    
    embedding_on_objects :=
      uniq_object -> SetOfObjects( SkeletalTransitiveLeftGSets )[1];
    
    embedding_on_morphisms :=
      { source, morG, target } -> MorphismConstructor( SkeletalTransitiveLeftGSets, source, UnderlyingGroupElement( morG ), target );
    
    return Triple( UnderlyingGroupAsCategory( SkeletalTransitiveLeftGSets ),
                   Pair( embedding_on_objects, embedding_on_morphisms ),
                   SkeletalTransitiveLeftGSets );
    
end );

##
InstallMethod( EmbeddingOfUnderlyingGroupAsCategory,
        "for a skeletal category of transitive left G-sets",
        [ IsSkeletalCategoryOfTransitiveLeftGSets ],
        
  function ( SkeletalTransitiveLeftGSets )
    local data, Y;
    
    data := EmbeddingOfUnderlyingGroupAsCategoryData( SkeletalTransitiveLeftGSets );
    
    Y := CapFunctor( "Embedding functor into the skeletal category of transitive left G-sets", data[1], SkeletalTransitiveLeftGSets );
    
    AddObjectFunction( Y, data[2][1] );
    
    AddMorphismFunction( Y, data[2][2] );
    
    return Y;
    
end );

##
InstallMethodForCompilerForCAP( ExtendFunctorToSkeletalCategoryOfTransitiveLeftGSetsData,
        "for a two categories and a pair of functions",
        [ IsSkeletalCategoryOfTransitiveLeftGSets, IsList, IsCategoryWithCoequalizers ],
        
  function ( SkeletalTransitiveLeftGSets, pair_of_funcs, category_with_coequalizers )
    local group_as_category, functor_on_objects, functor_on_morphisms, img_obj,
          extended_functor_on_objects, extended_functor_on_morphisms;
    
    group_as_category := UnderlyingGroupAsCategory( SkeletalTransitiveLeftGSets );
    
    functor_on_objects := pair_of_funcs[1];
    functor_on_morphisms := pair_of_funcs[2];
    
    img_obj := functor_on_objects( GroupAsCategoryUniqueObject( group_as_category ) );
    
    ## the code below is the doctrine-specific ur-algorithm for the coequalizer completion
    
    extended_functor_on_objects :=
      function ( obj_in_SkeletalTransitiveLeftGSets )
        local coeq_mors, automorphisms;
        
        coeq_mors := CoequalizerAutomorphisms( SkeletalTransitiveLeftGSets, obj_in_SkeletalTransitiveLeftGSets );
        
        automorphisms :=
          List( coeq_mors, g ->
                functor_on_morphisms(
                        img_obj,
                        g,
                        img_obj ) );
        
        return CoequalizerOfIdentityAndAutomorphisms( category_with_coequalizers, img_obj, automorphisms );
        
    end;
    
    extended_functor_on_morphisms :=
      function ( source, mor_in_SkeletalTransitiveLeftGSets, target )
        local coeq_mors_source, coeq_mors_target, automorphisms_source, automorphisms_target, g;
        
        coeq_mors_source := CoequalizerAutomorphisms( SkeletalTransitiveLeftGSets, Source( mor_in_SkeletalTransitiveLeftGSets ) );
        
        coeq_mors_target := CoequalizerAutomorphisms( SkeletalTransitiveLeftGSets, Target( mor_in_SkeletalTransitiveLeftGSets ) );
        
        automorphisms_source :=
          List( coeq_mors_source, g ->
                functor_on_morphisms(
                        img_obj,
                        g,
                        img_obj ) );
        
        automorphisms_target :=
          List( coeq_mors_target, g ->
                functor_on_morphisms(
                        img_obj,
                        g,
                        img_obj ) );
        
        if not IsEqualForObjects( category_with_coequalizers, source, CoequalizerOfIdentityAndAutomorphisms( category_with_coequalizers, img_obj, automorphisms_source ) ) then
            # COVERAGE_IGNORE_NEXT_LINE
            Error( "source and CoequalizerOfIdentityAndAutomorphisms( automorphisms_source ) do not coincide\n" );
        fi;
        
        if not IsEqualForObjects( category_with_coequalizers, target, CoequalizerOfIdentityAndAutomorphisms( category_with_coequalizers, img_obj, automorphisms_target ) ) then
            # COVERAGE_IGNORE_NEXT_LINE
            Error( "target and CoequalizerOfIdentityAndAutomorphisms( automorphisms_target ) do not coincide\n" );
        fi;
        
        g := GroupAsCategoryMorphism( group_as_category, UnderlyingGroupElement( mor_in_SkeletalTransitiveLeftGSets ) );
        
        return CoequalizerOfIdentityAndAutomorphismsFunctorialWithGivenCoequalizers( category_with_coequalizers,
                       source,
                       automorphisms_source,
                       functor_on_morphisms(
                               img_obj,
                               g,
                               img_obj ),
                       automorphisms_target,
                       target );
        
    end;
    
    return Triple( SkeletalTransitiveLeftGSets,
                   Pair( extended_functor_on_objects, extended_functor_on_morphisms ),
                   category_with_coequalizers );
    
end );

##
InstallMethod( ExtendFunctorToSkeletalCategoryOfTransitiveLeftGSets,
        "for a functor",
        [ IsCapFunctor ],
        
  function ( F )
    local C, D, SkeletalTransitiveLeftGSets, data, UF;
    
    C := SourceOfFunctor( F );
    D := RangeOfFunctor( F );
    
    SkeletalTransitiveLeftGSets := SkeletalCategoryOfTransitiveLeftGSets( C );
    
    data := ExtendFunctorToSkeletalCategoryOfTransitiveLeftGSetsData(
                    SkeletalTransitiveLeftGSets,
                    Pair( FunctorObjectOperation( F ), FunctorMorphismOperation( F ) ),
                    D );
    
    UF := CapFunctor( Concatenation( "Extension to SkeletalCategoryOfTransitiveLeftGSets( Source( ", Name( F ), " ) )" ), SkeletalTransitiveLeftGSets, D );
    
    AddObjectFunction( UF,
            data[2][1] );
    
    AddMorphismFunction( UF,
            data[2][2] );
    
    return UF;
    
end );

##################################
##
## String, View, and Display methods
##
##################################

##
InstallMethod( String,
        "for a skeletal transitive left G-set",
        [ IsObjectInSkeletalCategoryOfTransitiveLeftGSets ],
        
  function ( Omega )
    
    return Concatenation( CapCategory( Omega )!.name_of_group, " / U_", String( ObjectNumber( Omega ) ) );
    
end );

##
InstallMethod( ViewString,
        "for a skeletal transitive left G-set",
        [ IsObjectInSkeletalCategoryOfTransitiveLeftGSets ],
        
  function ( Omega )
    
    return String( Omega );
    
end );

##
InstallMethod( String,
        "for a morphism of skeletal transitive left G-sets",
        [ IsMorphismInSkeletalCategoryOfTransitiveLeftGSets ],
        
  function ( mor )
    
    return Concatenation( String( UnderlyingGroupElement( mor ) ), ": ", ViewString( Source( mor ) ), " -> ", ViewString( Target( mor ) ) );
    
end );

##
InstallMethod( ViewString,
        "for a morphism of skeletal transitive left G-sets",
        [ IsMorphismInSkeletalCategoryOfTransitiveLeftGSets ],
        
  function ( mor )
    
    return String( mor );
    
end );
