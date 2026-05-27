# SPDX-License-Identifier: GPL-2.0-or-later
# FinGSetsForCAP: The (skeletal) elementary topos of finite G-sets
#
# Implementations
#
BindGlobal( "ADD_FUNCTIONS_FOR_SkeletalCategoryOfTransitiveLeftGSets_precompiled", function ( cat )
    
    ##
    AddCoequalizer( cat,
        
########
function ( cat_1, Y_1, morphisms_1 )
    local hoisted_1_1, hoisted_2_1, hoisted_3_1, hoisted_4_1, deduped_8_1, deduped_9_1, deduped_10_1, deduped_11_1, deduped_12_1;
    deduped_12_1 := RepresentativesOfSubgroupsUpToConjugation( cat_1 );
    deduped_11_1 := UnderlyingGroup( cat_1 );
    deduped_10_1 := Length( morphisms_1 );
    deduped_9_1 := [ 1 .. deduped_10_1 ];
    hoisted_3_1 := List( deduped_9_1, function ( i_2 )
            return CAP_JIT_INCOMPLETE_LOGIC( UnderlyingGroupElement( CAP_JIT_INCOMPLETE_LOGIC( morphisms_1[i_2] ) ) );
        end );
    hoisted_2_1 := List( deduped_9_1, function ( i_2 )
            return CAP_JIT_INCOMPLETE_LOGIC( InverseImmutable( UnderlyingGroupElement( CAP_JIT_INCOMPLETE_LOGIC( morphisms_1[i_2] ) ) ) );
        end );
    deduped_8_1 := SubmagmaWithInverses( deduped_11_1, Concatenation( CAP_JIT_INCOMPLETE_LOGIC( GeneratorsOfMagmaWithInverses( CAP_JIT_INCOMPLETE_LOGIC( deduped_12_1[ObjectNumber( Y_1 )] ) ) ), List( [ 1 .. deduped_10_1 - 1 ], function ( i_2 )
                return MultiplyGroupElements( hoisted_2_1[i_2], hoisted_3_1[i_2 + 1] );
            end ) ) );
    hoisted_4_1 := Index( deduped_11_1, deduped_8_1 );
    hoisted_1_1 := CardinalitiesOfObjects( cat_1 );
    return CreateCapCategoryObjectWithAttributes( cat_1, ObjectNumber, SafeFirst( Filtered( [ 1 .. NumberOfObjects( cat_1 ) ], function ( i_2 )
                return hoisted_1_1[i_2] = hoisted_4_1;
            end ), function ( c_2 )
              return IsConjugate( deduped_11_1, deduped_8_1, deduped_12_1[c_2] );
          end ) );
end
########
        
    , 101 : IsPrecompiledDerivation := true );
    
    ##
    cat!.cached_precompiled_functions.Coequalizer :=
        
########
function ( cat_1, Y_1, morphisms_1 )
    local hoisted_1_1, hoisted_2_1, hoisted_3_1, hoisted_4_1, hoisted_5_1, hoisted_6_1, deduped_10_1, deduped_11_1, deduped_12_1, deduped_13_1, deduped_14_1;
    deduped_14_1 := RepresentativesOfSubgroupsUpToConjugation( cat_1 );
    deduped_13_1 := UnderlyingGroup( cat_1 );
    deduped_12_1 := Length( morphisms_1 );
    deduped_11_1 := [ 1 .. deduped_12_1 ];
    hoisted_4_1 := List( morphisms_1, UnderlyingGroupElement );
    hoisted_5_1 := List( deduped_11_1, function ( i_2 )
            return hoisted_4_1[i_2];
        end );
    hoisted_2_1 := List( morphisms_1, function ( x_2 )
            return InverseImmutable( UnderlyingGroupElement( x_2 ) );
        end );
    hoisted_3_1 := List( deduped_11_1, function ( i_2 )
            return hoisted_2_1[i_2];
        end );
    deduped_10_1 := SubmagmaWithInverses( deduped_13_1, Concatenation( List( deduped_14_1, GeneratorsOfMagmaWithInverses )[ObjectNumber( Y_1 )], List( [ 1 .. deduped_12_1 - 1 ], function ( i_2 )
                return MultiplyGroupElements( hoisted_3_1[i_2], hoisted_5_1[i_2 + 1] );
            end ) ) );
    hoisted_6_1 := Index( deduped_13_1, deduped_10_1 );
    hoisted_1_1 := CardinalitiesOfObjects( cat_1 );
    return CreateCapCategoryObjectWithAttributes( cat_1, ObjectNumber, SafeFirst( Filtered( [ 1 .. NumberOfObjects( cat_1 ) ], function ( i_2 )
                return hoisted_1_1[i_2] = hoisted_6_1;
            end ), function ( c_2 )
              return IsConjugate( deduped_13_1, deduped_10_1, deduped_14_1[c_2] );
          end ) );
end
########
        
    ;
    
    ##
    AddCoequalizerFunctorial( cat,
        
########
function ( cat_1, morphisms_1, mu_1, morphismsp_1 )
    local deduped_1_1, hoisted_2_1, hoisted_3_1, hoisted_4_1, hoisted_8_1, hoisted_9_1, hoisted_10_1, deduped_12_1, deduped_13_1, deduped_14_1, deduped_15_1, deduped_16_1, deduped_17_1, deduped_18_1, deduped_19_1, deduped_20_1, deduped_21_1, deduped_22_1, deduped_23_1;
    deduped_23_1 := Length( morphismsp_1 );
    deduped_22_1 := Length( morphisms_1 );
    deduped_21_1 := RepresentativesOfSubgroupsUpToConjugation( cat_1 );
    deduped_20_1 := UnderlyingGroup( cat_1 );
    deduped_19_1 := [ 1 .. deduped_23_1 ];
    deduped_18_1 := [ 1 .. deduped_22_1 ];
    deduped_17_1 := [ 1 .. NumberOfObjects( cat_1 ) ];
    deduped_16_1 := List( deduped_21_1, GeneratorsOfMagmaWithInverses );
    hoisted_9_1 := List( deduped_19_1, function ( i_2 )
            return CAP_JIT_INCOMPLETE_LOGIC( UnderlyingGroupElement( CAP_JIT_INCOMPLETE_LOGIC( morphismsp_1[i_2] ) ) );
        end );
    hoisted_8_1 := List( deduped_19_1, function ( i_2 )
            return CAP_JIT_INCOMPLETE_LOGIC( InverseImmutable( UnderlyingGroupElement( CAP_JIT_INCOMPLETE_LOGIC( morphismsp_1[i_2] ) ) ) );
        end );
    deduped_13_1 := SubmagmaWithInverses( deduped_20_1, Concatenation( deduped_16_1[ObjectNumber( Range( mu_1 ) )], List( [ 1 .. deduped_23_1 - 1 ], function ( i_2 )
                return MultiplyGroupElements( hoisted_8_1[i_2], hoisted_9_1[i_2 + 1] );
            end ) ) );
    hoisted_10_1 := Index( deduped_20_1, deduped_13_1 );
    deduped_1_1 := CardinalitiesOfObjects( cat_1 );
    deduped_15_1 := SafeFirst( Filtered( deduped_17_1, function ( i_2 )
              return deduped_1_1[i_2] = hoisted_10_1;
          end ), function ( c_2 )
            return IsConjugate( deduped_20_1, deduped_13_1, deduped_21_1[c_2] );
        end );
    hoisted_3_1 := List( deduped_18_1, function ( i_2 )
            return CAP_JIT_INCOMPLETE_LOGIC( UnderlyingGroupElement( CAP_JIT_INCOMPLETE_LOGIC( morphisms_1[i_2] ) ) );
        end );
    hoisted_2_1 := List( deduped_18_1, function ( i_2 )
            return CAP_JIT_INCOMPLETE_LOGIC( InverseImmutable( UnderlyingGroupElement( CAP_JIT_INCOMPLETE_LOGIC( morphisms_1[i_2] ) ) ) );
        end );
    deduped_12_1 := SubmagmaWithInverses( deduped_20_1, Concatenation( deduped_16_1[ObjectNumber( Source( mu_1 ) )], List( [ 1 .. deduped_22_1 - 1 ], function ( i_2 )
                return MultiplyGroupElements( hoisted_2_1[i_2], hoisted_3_1[i_2 + 1] );
            end ) ) );
    hoisted_4_1 := Index( deduped_20_1, deduped_12_1 );
    deduped_14_1 := SafeFirst( Filtered( deduped_17_1, function ( i_2 )
              return deduped_1_1[i_2] = hoisted_4_1;
          end ), function ( c_2 )
            return IsConjugate( deduped_20_1, deduped_12_1, deduped_21_1[c_2] );
        end );
    return CreateCapCategoryMorphismWithAttributes( cat_1, CreateCapCategoryObjectWithAttributes( cat_1, ObjectNumber, deduped_14_1 ), CreateCapCategoryObjectWithAttributes( cat_1, ObjectNumber, deduped_15_1 ), UnderlyingGroupElement, MultiplyGroupElements( InverseImmutable( RepresentativeAction( deduped_20_1, deduped_12_1, deduped_21_1[deduped_14_1] ) ), MultiplyGroupElements( UnderlyingGroupElement( mu_1 ), RepresentativeAction( deduped_20_1, deduped_13_1, deduped_21_1[deduped_15_1] ) ) ) );
end
########
        
    , 609 : IsPrecompiledDerivation := true );
    
    ##
    cat!.cached_precompiled_functions.CoequalizerFunctorial :=
        
########
function ( cat_1, morphisms_1, mu_1, morphismsp_1 )
    local deduped_1_1, hoisted_2_1, hoisted_3_1, hoisted_4_1, hoisted_5_1, hoisted_6_1, hoisted_10_1, hoisted_11_1, hoisted_12_1, hoisted_13_1, hoisted_14_1, deduped_16_1, deduped_17_1, deduped_18_1, deduped_19_1, deduped_20_1, deduped_21_1, deduped_22_1, deduped_23_1, deduped_24_1, deduped_25_1, deduped_26_1, deduped_27_1;
    deduped_27_1 := Length( morphismsp_1 );
    deduped_26_1 := Length( morphisms_1 );
    deduped_25_1 := RepresentativesOfSubgroupsUpToConjugation( cat_1 );
    deduped_24_1 := UnderlyingGroup( cat_1 );
    deduped_23_1 := [ 1 .. deduped_27_1 ];
    deduped_22_1 := [ 1 .. deduped_26_1 ];
    deduped_21_1 := [ 1 .. NumberOfObjects( cat_1 ) ];
    deduped_20_1 := List( deduped_25_1, GeneratorsOfMagmaWithInverses );
    hoisted_12_1 := List( morphismsp_1, UnderlyingGroupElement );
    hoisted_13_1 := List( deduped_23_1, function ( i_2 )
            return hoisted_12_1[i_2];
        end );
    hoisted_10_1 := List( morphismsp_1, function ( x_2 )
            return InverseImmutable( UnderlyingGroupElement( x_2 ) );
        end );
    hoisted_11_1 := List( deduped_23_1, function ( i_2 )
            return hoisted_10_1[i_2];
        end );
    deduped_17_1 := SubmagmaWithInverses( deduped_24_1, Concatenation( deduped_20_1[ObjectNumber( Range( mu_1 ) )], List( [ 1 .. deduped_27_1 - 1 ], function ( i_2 )
                return MultiplyGroupElements( hoisted_11_1[i_2], hoisted_13_1[i_2 + 1] );
            end ) ) );
    hoisted_14_1 := Index( deduped_24_1, deduped_17_1 );
    deduped_1_1 := CardinalitiesOfObjects( cat_1 );
    deduped_19_1 := SafeFirst( Filtered( deduped_21_1, function ( i_2 )
              return deduped_1_1[i_2] = hoisted_14_1;
          end ), function ( c_2 )
            return IsConjugate( deduped_24_1, deduped_17_1, deduped_25_1[c_2] );
        end );
    hoisted_4_1 := List( morphisms_1, UnderlyingGroupElement );
    hoisted_5_1 := List( deduped_22_1, function ( i_2 )
            return hoisted_4_1[i_2];
        end );
    hoisted_2_1 := List( morphisms_1, function ( x_2 )
            return InverseImmutable( UnderlyingGroupElement( x_2 ) );
        end );
    hoisted_3_1 := List( deduped_22_1, function ( i_2 )
            return hoisted_2_1[i_2];
        end );
    deduped_16_1 := SubmagmaWithInverses( deduped_24_1, Concatenation( deduped_20_1[ObjectNumber( Source( mu_1 ) )], List( [ 1 .. deduped_26_1 - 1 ], function ( i_2 )
                return MultiplyGroupElements( hoisted_3_1[i_2], hoisted_5_1[i_2 + 1] );
            end ) ) );
    hoisted_6_1 := Index( deduped_24_1, deduped_16_1 );
    deduped_18_1 := SafeFirst( Filtered( deduped_21_1, function ( i_2 )
              return deduped_1_1[i_2] = hoisted_6_1;
          end ), function ( c_2 )
            return IsConjugate( deduped_24_1, deduped_16_1, deduped_25_1[c_2] );
        end );
    return CreateCapCategoryMorphismWithAttributes( cat_1, CreateCapCategoryObjectWithAttributes( cat_1, ObjectNumber, deduped_18_1 ), CreateCapCategoryObjectWithAttributes( cat_1, ObjectNumber, deduped_19_1 ), UnderlyingGroupElement, MultiplyGroupElements( InverseImmutable( RepresentativeAction( deduped_24_1, deduped_16_1, deduped_25_1[deduped_18_1] ) ), MultiplyGroupElements( UnderlyingGroupElement( mu_1 ), RepresentativeAction( deduped_24_1, deduped_17_1, deduped_25_1[deduped_19_1] ) ) ) );
end
########
        
    ;
    
    ##
    AddCoequalizerFunctorialWithGivenCoequalizers( cat,
        
########
function ( cat_1, P_1, morphisms_1, mu_1, morphismsp_1, Pp_1 )
    local deduped_1_1, hoisted_2_1, hoisted_3_1, hoisted_4_1, hoisted_8_1, hoisted_9_1, hoisted_10_1, deduped_12_1, deduped_13_1, deduped_14_1, deduped_15_1, deduped_16_1, deduped_17_1, deduped_18_1, deduped_19_1, deduped_20_1, deduped_21_1, deduped_22_1, deduped_23_1;
    deduped_23_1 := Length( morphismsp_1 );
    deduped_22_1 := Length( morphisms_1 );
    deduped_21_1 := RepresentativesOfSubgroupsUpToConjugation( cat_1 );
    deduped_20_1 := UnderlyingGroup( cat_1 );
    deduped_19_1 := [ 1 .. deduped_23_1 ];
    deduped_18_1 := [ 1 .. deduped_22_1 ];
    deduped_17_1 := [ 1 .. NumberOfObjects( cat_1 ) ];
    deduped_16_1 := List( deduped_21_1, GeneratorsOfMagmaWithInverses );
    hoisted_9_1 := List( deduped_19_1, function ( i_2 )
            return CAP_JIT_INCOMPLETE_LOGIC( UnderlyingGroupElement( CAP_JIT_INCOMPLETE_LOGIC( morphismsp_1[i_2] ) ) );
        end );
    hoisted_8_1 := List( deduped_19_1, function ( i_2 )
            return CAP_JIT_INCOMPLETE_LOGIC( InverseImmutable( UnderlyingGroupElement( CAP_JIT_INCOMPLETE_LOGIC( morphismsp_1[i_2] ) ) ) );
        end );
    deduped_13_1 := SubmagmaWithInverses( deduped_20_1, Concatenation( deduped_16_1[ObjectNumber( Range( mu_1 ) )], List( [ 1 .. deduped_23_1 - 1 ], function ( i_2 )
                return MultiplyGroupElements( hoisted_8_1[i_2], hoisted_9_1[i_2 + 1] );
            end ) ) );
    hoisted_10_1 := Index( deduped_20_1, deduped_13_1 );
    deduped_1_1 := CardinalitiesOfObjects( cat_1 );
    deduped_15_1 := SafeFirst( Filtered( deduped_17_1, function ( i_2 )
              return deduped_1_1[i_2] = hoisted_10_1;
          end ), function ( c_2 )
            return IsConjugate( deduped_20_1, deduped_13_1, deduped_21_1[c_2] );
        end );
    hoisted_3_1 := List( deduped_18_1, function ( i_2 )
            return CAP_JIT_INCOMPLETE_LOGIC( UnderlyingGroupElement( CAP_JIT_INCOMPLETE_LOGIC( morphisms_1[i_2] ) ) );
        end );
    hoisted_2_1 := List( deduped_18_1, function ( i_2 )
            return CAP_JIT_INCOMPLETE_LOGIC( InverseImmutable( UnderlyingGroupElement( CAP_JIT_INCOMPLETE_LOGIC( morphisms_1[i_2] ) ) ) );
        end );
    deduped_12_1 := SubmagmaWithInverses( deduped_20_1, Concatenation( deduped_16_1[ObjectNumber( Source( mu_1 ) )], List( [ 1 .. deduped_22_1 - 1 ], function ( i_2 )
                return MultiplyGroupElements( hoisted_2_1[i_2], hoisted_3_1[i_2 + 1] );
            end ) ) );
    hoisted_4_1 := Index( deduped_20_1, deduped_12_1 );
    deduped_14_1 := SafeFirst( Filtered( deduped_17_1, function ( i_2 )
              return deduped_1_1[i_2] = hoisted_4_1;
          end ), function ( c_2 )
            return IsConjugate( deduped_20_1, deduped_12_1, deduped_21_1[c_2] );
        end );
    return CreateCapCategoryMorphismWithAttributes( cat_1, CreateCapCategoryObjectWithAttributes( cat_1, ObjectNumber, deduped_14_1 ), CreateCapCategoryObjectWithAttributes( cat_1, ObjectNumber, deduped_15_1 ), UnderlyingGroupElement, MultiplyGroupElements( InverseImmutable( RepresentativeAction( deduped_20_1, deduped_12_1, deduped_21_1[deduped_14_1] ) ), MultiplyGroupElements( UnderlyingGroupElement( mu_1 ), RepresentativeAction( deduped_20_1, deduped_13_1, deduped_21_1[deduped_15_1] ) ) ) );
end
########
        
    , 406 : IsPrecompiledDerivation := true );
    
    ##
    cat!.cached_precompiled_functions.CoequalizerFunctorialWithGivenCoequalizers :=
        
########
function ( cat_1, P_1, morphisms_1, mu_1, morphismsp_1, Pp_1 )
    local deduped_1_1, hoisted_2_1, hoisted_3_1, hoisted_4_1, hoisted_5_1, hoisted_6_1, hoisted_10_1, hoisted_11_1, hoisted_12_1, hoisted_13_1, hoisted_14_1, deduped_16_1, deduped_17_1, deduped_18_1, deduped_19_1, deduped_20_1, deduped_21_1, deduped_22_1, deduped_23_1, deduped_24_1, deduped_25_1, deduped_26_1, deduped_27_1;
    deduped_27_1 := Length( morphismsp_1 );
    deduped_26_1 := Length( morphisms_1 );
    deduped_25_1 := RepresentativesOfSubgroupsUpToConjugation( cat_1 );
    deduped_24_1 := UnderlyingGroup( cat_1 );
    deduped_23_1 := [ 1 .. deduped_27_1 ];
    deduped_22_1 := [ 1 .. deduped_26_1 ];
    deduped_21_1 := [ 1 .. NumberOfObjects( cat_1 ) ];
    deduped_20_1 := List( deduped_25_1, GeneratorsOfMagmaWithInverses );
    hoisted_12_1 := List( morphismsp_1, UnderlyingGroupElement );
    hoisted_13_1 := List( deduped_23_1, function ( i_2 )
            return hoisted_12_1[i_2];
        end );
    hoisted_10_1 := List( morphismsp_1, function ( x_2 )
            return InverseImmutable( UnderlyingGroupElement( x_2 ) );
        end );
    hoisted_11_1 := List( deduped_23_1, function ( i_2 )
            return hoisted_10_1[i_2];
        end );
    deduped_17_1 := SubmagmaWithInverses( deduped_24_1, Concatenation( deduped_20_1[ObjectNumber( Range( mu_1 ) )], List( [ 1 .. deduped_27_1 - 1 ], function ( i_2 )
                return MultiplyGroupElements( hoisted_11_1[i_2], hoisted_13_1[i_2 + 1] );
            end ) ) );
    hoisted_14_1 := Index( deduped_24_1, deduped_17_1 );
    deduped_1_1 := CardinalitiesOfObjects( cat_1 );
    deduped_19_1 := SafeFirst( Filtered( deduped_21_1, function ( i_2 )
              return deduped_1_1[i_2] = hoisted_14_1;
          end ), function ( c_2 )
            return IsConjugate( deduped_24_1, deduped_17_1, deduped_25_1[c_2] );
        end );
    hoisted_4_1 := List( morphisms_1, UnderlyingGroupElement );
    hoisted_5_1 := List( deduped_22_1, function ( i_2 )
            return hoisted_4_1[i_2];
        end );
    hoisted_2_1 := List( morphisms_1, function ( x_2 )
            return InverseImmutable( UnderlyingGroupElement( x_2 ) );
        end );
    hoisted_3_1 := List( deduped_22_1, function ( i_2 )
            return hoisted_2_1[i_2];
        end );
    deduped_16_1 := SubmagmaWithInverses( deduped_24_1, Concatenation( deduped_20_1[ObjectNumber( Source( mu_1 ) )], List( [ 1 .. deduped_26_1 - 1 ], function ( i_2 )
                return MultiplyGroupElements( hoisted_3_1[i_2], hoisted_5_1[i_2 + 1] );
            end ) ) );
    hoisted_6_1 := Index( deduped_24_1, deduped_16_1 );
    deduped_18_1 := SafeFirst( Filtered( deduped_21_1, function ( i_2 )
              return deduped_1_1[i_2] = hoisted_6_1;
          end ), function ( c_2 )
            return IsConjugate( deduped_24_1, deduped_16_1, deduped_25_1[c_2] );
        end );
    return CreateCapCategoryMorphismWithAttributes( cat_1, CreateCapCategoryObjectWithAttributes( cat_1, ObjectNumber, deduped_18_1 ), CreateCapCategoryObjectWithAttributes( cat_1, ObjectNumber, deduped_19_1 ), UnderlyingGroupElement, MultiplyGroupElements( InverseImmutable( RepresentativeAction( deduped_24_1, deduped_16_1, deduped_25_1[deduped_18_1] ) ), MultiplyGroupElements( UnderlyingGroupElement( mu_1 ), RepresentativeAction( deduped_24_1, deduped_17_1, deduped_25_1[deduped_19_1] ) ) ) );
end
########
        
    ;
    
    ##
    AddCoequalizerOfIdentityAndAutomorphisms( cat,
        
########
function ( cat_1, Y_1, automorphisms_1 )
    local hoisted_1_1, hoisted_2_1, deduped_6_1, deduped_7_1, deduped_8_1;
    deduped_8_1 := RepresentativesOfSubgroupsUpToConjugation( cat_1 );
    deduped_7_1 := UnderlyingGroup( cat_1 );
    deduped_6_1 := SubmagmaWithInverses( deduped_7_1, Concatenation( CAP_JIT_INCOMPLETE_LOGIC( GeneratorsOfMagmaWithInverses( CAP_JIT_INCOMPLETE_LOGIC( deduped_8_1[ObjectNumber( Y_1 )] ) ) ), List( [ 1 .. Length( automorphisms_1 ) ], function ( i_2 )
                return CAP_JIT_INCOMPLETE_LOGIC( UnderlyingGroupElement( CAP_JIT_INCOMPLETE_LOGIC( automorphisms_1[i_2] ) ) );
            end ) ) );
    hoisted_2_1 := Index( deduped_7_1, deduped_6_1 );
    hoisted_1_1 := CardinalitiesOfObjects( cat_1 );
    return CreateCapCategoryObjectWithAttributes( cat_1, ObjectNumber, SafeFirst( Filtered( [ 1 .. NumberOfObjects( cat_1 ) ], function ( i_2 )
                return hoisted_1_1[i_2] = hoisted_2_1;
            end ), function ( c_2 )
              return IsConjugate( deduped_7_1, deduped_6_1, deduped_8_1[c_2] );
          end ) );
end
########
        
    , 101 : IsPrecompiledDerivation := true );
    
    ##
    cat!.cached_precompiled_functions.CoequalizerOfIdentityAndAutomorphisms :=
        
########
function ( cat_1, Y_1, automorphisms_1 )
    local hoisted_1_1, hoisted_2_1, hoisted_3_1, deduped_7_1, deduped_8_1, deduped_9_1;
    deduped_9_1 := RepresentativesOfSubgroupsUpToConjugation( cat_1 );
    deduped_8_1 := UnderlyingGroup( cat_1 );
    hoisted_2_1 := List( automorphisms_1, UnderlyingGroupElement );
    deduped_7_1 := SubmagmaWithInverses( deduped_8_1, Concatenation( List( deduped_9_1, GeneratorsOfMagmaWithInverses )[ObjectNumber( Y_1 )], List( [ 1 .. Length( automorphisms_1 ) ], function ( i_2 )
                return hoisted_2_1[i_2];
            end ) ) );
    hoisted_3_1 := Index( deduped_8_1, deduped_7_1 );
    hoisted_1_1 := CardinalitiesOfObjects( cat_1 );
    return CreateCapCategoryObjectWithAttributes( cat_1, ObjectNumber, SafeFirst( Filtered( [ 1 .. NumberOfObjects( cat_1 ) ], function ( i_2 )
                return hoisted_1_1[i_2] = hoisted_3_1;
            end ), function ( c_2 )
              return IsConjugate( deduped_8_1, deduped_7_1, deduped_9_1[c_2] );
          end ) );
end
########
        
    ;
    
    ##
    AddCoequalizerOfIdentityAndAutomorphismsFunctorial( cat,
        
########
function ( cat_1, automorphisms_1, mu_1, automorphismsp_1 )
    local deduped_1_1, hoisted_2_1, hoisted_6_1, deduped_8_1, deduped_9_1, deduped_10_1, deduped_11_1, deduped_12_1, deduped_13_1, deduped_14_1, deduped_15_1;
    deduped_15_1 := RepresentativesOfSubgroupsUpToConjugation( cat_1 );
    deduped_14_1 := UnderlyingGroup( cat_1 );
    deduped_13_1 := [ 1 .. NumberOfObjects( cat_1 ) ];
    deduped_12_1 := List( deduped_15_1, GeneratorsOfMagmaWithInverses );
    deduped_9_1 := SubmagmaWithInverses( deduped_14_1, Concatenation( deduped_12_1[ObjectNumber( Range( mu_1 ) )], List( [ 1 .. Length( automorphismsp_1 ) ], function ( i_2 )
                return CAP_JIT_INCOMPLETE_LOGIC( UnderlyingGroupElement( CAP_JIT_INCOMPLETE_LOGIC( automorphismsp_1[i_2] ) ) );
            end ) ) );
    hoisted_6_1 := Index( deduped_14_1, deduped_9_1 );
    deduped_1_1 := CardinalitiesOfObjects( cat_1 );
    deduped_11_1 := SafeFirst( Filtered( deduped_13_1, function ( i_2 )
              return deduped_1_1[i_2] = hoisted_6_1;
          end ), function ( c_2 )
            return IsConjugate( deduped_14_1, deduped_9_1, deduped_15_1[c_2] );
        end );
    deduped_8_1 := SubmagmaWithInverses( deduped_14_1, Concatenation( deduped_12_1[ObjectNumber( Source( mu_1 ) )], List( [ 1 .. Length( automorphisms_1 ) ], function ( i_2 )
                return CAP_JIT_INCOMPLETE_LOGIC( UnderlyingGroupElement( CAP_JIT_INCOMPLETE_LOGIC( automorphisms_1[i_2] ) ) );
            end ) ) );
    hoisted_2_1 := Index( deduped_14_1, deduped_8_1 );
    deduped_10_1 := SafeFirst( Filtered( deduped_13_1, function ( i_2 )
              return deduped_1_1[i_2] = hoisted_2_1;
          end ), function ( c_2 )
            return IsConjugate( deduped_14_1, deduped_8_1, deduped_15_1[c_2] );
        end );
    return CreateCapCategoryMorphismWithAttributes( cat_1, CreateCapCategoryObjectWithAttributes( cat_1, ObjectNumber, deduped_10_1 ), CreateCapCategoryObjectWithAttributes( cat_1, ObjectNumber, deduped_11_1 ), UnderlyingGroupElement, MultiplyGroupElements( InverseImmutable( RepresentativeAction( deduped_14_1, deduped_8_1, deduped_15_1[deduped_10_1] ) ), MultiplyGroupElements( UnderlyingGroupElement( mu_1 ), RepresentativeAction( deduped_14_1, deduped_9_1, deduped_15_1[deduped_11_1] ) ) ) );
end
########
        
    , 608 : IsPrecompiledDerivation := true );
    
    ##
    cat!.cached_precompiled_functions.CoequalizerOfIdentityAndAutomorphismsFunctorial :=
        
########
function ( cat_1, automorphisms_1, mu_1, automorphismsp_1 )
    local deduped_1_1, hoisted_2_1, hoisted_3_1, hoisted_7_1, hoisted_8_1, deduped_10_1, deduped_11_1, deduped_12_1, deduped_13_1, deduped_14_1, deduped_15_1, deduped_16_1, deduped_17_1;
    deduped_17_1 := RepresentativesOfSubgroupsUpToConjugation( cat_1 );
    deduped_16_1 := UnderlyingGroup( cat_1 );
    deduped_15_1 := [ 1 .. NumberOfObjects( cat_1 ) ];
    deduped_14_1 := List( deduped_17_1, GeneratorsOfMagmaWithInverses );
    hoisted_7_1 := List( automorphismsp_1, UnderlyingGroupElement );
    deduped_11_1 := SubmagmaWithInverses( deduped_16_1, Concatenation( deduped_14_1[ObjectNumber( Range( mu_1 ) )], List( [ 1 .. Length( automorphismsp_1 ) ], function ( i_2 )
                return hoisted_7_1[i_2];
            end ) ) );
    hoisted_8_1 := Index( deduped_16_1, deduped_11_1 );
    deduped_1_1 := CardinalitiesOfObjects( cat_1 );
    deduped_13_1 := SafeFirst( Filtered( deduped_15_1, function ( i_2 )
              return deduped_1_1[i_2] = hoisted_8_1;
          end ), function ( c_2 )
            return IsConjugate( deduped_16_1, deduped_11_1, deduped_17_1[c_2] );
        end );
    hoisted_2_1 := List( automorphisms_1, UnderlyingGroupElement );
    deduped_10_1 := SubmagmaWithInverses( deduped_16_1, Concatenation( deduped_14_1[ObjectNumber( Source( mu_1 ) )], List( [ 1 .. Length( automorphisms_1 ) ], function ( i_2 )
                return hoisted_2_1[i_2];
            end ) ) );
    hoisted_3_1 := Index( deduped_16_1, deduped_10_1 );
    deduped_12_1 := SafeFirst( Filtered( deduped_15_1, function ( i_2 )
              return deduped_1_1[i_2] = hoisted_3_1;
          end ), function ( c_2 )
            return IsConjugate( deduped_16_1, deduped_10_1, deduped_17_1[c_2] );
        end );
    return CreateCapCategoryMorphismWithAttributes( cat_1, CreateCapCategoryObjectWithAttributes( cat_1, ObjectNumber, deduped_12_1 ), CreateCapCategoryObjectWithAttributes( cat_1, ObjectNumber, deduped_13_1 ), UnderlyingGroupElement, MultiplyGroupElements( InverseImmutable( RepresentativeAction( deduped_16_1, deduped_10_1, deduped_17_1[deduped_12_1] ) ), MultiplyGroupElements( UnderlyingGroupElement( mu_1 ), RepresentativeAction( deduped_16_1, deduped_11_1, deduped_17_1[deduped_13_1] ) ) ) );
end
########
        
    ;
    
    ##
    AddCoequalizerOfIdentityAndAutomorphismsFunctorialWithGivenCoequalizers( cat,
        
########
function ( cat_1, P_1, automorphisms_1, mu_1, automorphismsp_1, Pp_1 )
    local deduped_1_1, hoisted_2_1, hoisted_6_1, deduped_8_1, deduped_9_1, deduped_10_1, deduped_11_1, deduped_12_1, deduped_13_1, deduped_14_1, deduped_15_1;
    deduped_15_1 := RepresentativesOfSubgroupsUpToConjugation( cat_1 );
    deduped_14_1 := UnderlyingGroup( cat_1 );
    deduped_13_1 := [ 1 .. NumberOfObjects( cat_1 ) ];
    deduped_12_1 := List( deduped_15_1, GeneratorsOfMagmaWithInverses );
    deduped_9_1 := SubmagmaWithInverses( deduped_14_1, Concatenation( deduped_12_1[ObjectNumber( Range( mu_1 ) )], List( [ 1 .. Length( automorphismsp_1 ) ], function ( i_2 )
                return CAP_JIT_INCOMPLETE_LOGIC( UnderlyingGroupElement( CAP_JIT_INCOMPLETE_LOGIC( automorphismsp_1[i_2] ) ) );
            end ) ) );
    hoisted_6_1 := Index( deduped_14_1, deduped_9_1 );
    deduped_1_1 := CardinalitiesOfObjects( cat_1 );
    deduped_11_1 := SafeFirst( Filtered( deduped_13_1, function ( i_2 )
              return deduped_1_1[i_2] = hoisted_6_1;
          end ), function ( c_2 )
            return IsConjugate( deduped_14_1, deduped_9_1, deduped_15_1[c_2] );
        end );
    deduped_8_1 := SubmagmaWithInverses( deduped_14_1, Concatenation( deduped_12_1[ObjectNumber( Source( mu_1 ) )], List( [ 1 .. Length( automorphisms_1 ) ], function ( i_2 )
                return CAP_JIT_INCOMPLETE_LOGIC( UnderlyingGroupElement( CAP_JIT_INCOMPLETE_LOGIC( automorphisms_1[i_2] ) ) );
            end ) ) );
    hoisted_2_1 := Index( deduped_14_1, deduped_8_1 );
    deduped_10_1 := SafeFirst( Filtered( deduped_13_1, function ( i_2 )
              return deduped_1_1[i_2] = hoisted_2_1;
          end ), function ( c_2 )
            return IsConjugate( deduped_14_1, deduped_8_1, deduped_15_1[c_2] );
        end );
    return CreateCapCategoryMorphismWithAttributes( cat_1, CreateCapCategoryObjectWithAttributes( cat_1, ObjectNumber, deduped_10_1 ), CreateCapCategoryObjectWithAttributes( cat_1, ObjectNumber, deduped_11_1 ), UnderlyingGroupElement, MultiplyGroupElements( InverseImmutable( RepresentativeAction( deduped_14_1, deduped_8_1, deduped_15_1[deduped_10_1] ) ), MultiplyGroupElements( UnderlyingGroupElement( mu_1 ), RepresentativeAction( deduped_14_1, deduped_9_1, deduped_15_1[deduped_11_1] ) ) ) );
end
########
        
    , 405 : IsPrecompiledDerivation := true );
    
    ##
    cat!.cached_precompiled_functions.CoequalizerOfIdentityAndAutomorphismsFunctorialWithGivenCoequalizers :=
        
########
function ( cat_1, P_1, automorphisms_1, mu_1, automorphismsp_1, Pp_1 )
    local deduped_1_1, hoisted_2_1, hoisted_3_1, hoisted_7_1, hoisted_8_1, deduped_10_1, deduped_11_1, deduped_12_1, deduped_13_1, deduped_14_1, deduped_15_1, deduped_16_1, deduped_17_1;
    deduped_17_1 := RepresentativesOfSubgroupsUpToConjugation( cat_1 );
    deduped_16_1 := UnderlyingGroup( cat_1 );
    deduped_15_1 := [ 1 .. NumberOfObjects( cat_1 ) ];
    deduped_14_1 := List( deduped_17_1, GeneratorsOfMagmaWithInverses );
    hoisted_7_1 := List( automorphismsp_1, UnderlyingGroupElement );
    deduped_11_1 := SubmagmaWithInverses( deduped_16_1, Concatenation( deduped_14_1[ObjectNumber( Range( mu_1 ) )], List( [ 1 .. Length( automorphismsp_1 ) ], function ( i_2 )
                return hoisted_7_1[i_2];
            end ) ) );
    hoisted_8_1 := Index( deduped_16_1, deduped_11_1 );
    deduped_1_1 := CardinalitiesOfObjects( cat_1 );
    deduped_13_1 := SafeFirst( Filtered( deduped_15_1, function ( i_2 )
              return deduped_1_1[i_2] = hoisted_8_1;
          end ), function ( c_2 )
            return IsConjugate( deduped_16_1, deduped_11_1, deduped_17_1[c_2] );
        end );
    hoisted_2_1 := List( automorphisms_1, UnderlyingGroupElement );
    deduped_10_1 := SubmagmaWithInverses( deduped_16_1, Concatenation( deduped_14_1[ObjectNumber( Source( mu_1 ) )], List( [ 1 .. Length( automorphisms_1 ) ], function ( i_2 )
                return hoisted_2_1[i_2];
            end ) ) );
    hoisted_3_1 := Index( deduped_16_1, deduped_10_1 );
    deduped_12_1 := SafeFirst( Filtered( deduped_15_1, function ( i_2 )
              return deduped_1_1[i_2] = hoisted_3_1;
          end ), function ( c_2 )
            return IsConjugate( deduped_16_1, deduped_10_1, deduped_17_1[c_2] );
        end );
    return CreateCapCategoryMorphismWithAttributes( cat_1, CreateCapCategoryObjectWithAttributes( cat_1, ObjectNumber, deduped_12_1 ), CreateCapCategoryObjectWithAttributes( cat_1, ObjectNumber, deduped_13_1 ), UnderlyingGroupElement, MultiplyGroupElements( InverseImmutable( RepresentativeAction( deduped_16_1, deduped_10_1, deduped_17_1[deduped_12_1] ) ), MultiplyGroupElements( UnderlyingGroupElement( mu_1 ), RepresentativeAction( deduped_16_1, deduped_11_1, deduped_17_1[deduped_13_1] ) ) ) );
end
########
        
    ;
    
    ##
    AddColift( cat,
        
########
function ( cat_1, alpha_1, beta_1 )
    return CreateCapCategoryMorphismWithAttributes( cat_1, Range( alpha_1 ), Range( beta_1 ), UnderlyingGroupElement, MultiplyGroupElements( InverseImmutable( UnderlyingGroupElement( alpha_1 ) ), UnderlyingGroupElement( beta_1 ) ) );
end
########
        
    , 100 );
    
    ##
    AddColiftAlongEpimorphism( cat,
        
########
function ( cat_1, epsilon_1, tau_1 )
    return CreateCapCategoryMorphismWithAttributes( cat_1, Range( epsilon_1 ), Range( tau_1 ), UnderlyingGroupElement, MultiplyGroupElements( InverseImmutable( UnderlyingGroupElement( epsilon_1 ) ), UnderlyingGroupElement( tau_1 ) ) );
end
########
        
    , 101 : IsPrecompiledDerivation := true );
    
    ##
    AddDistinguishedObjectOfHomomorphismStructure( cat,
        
########
function ( cat_1 )
    return CreateCapCategoryObjectWithAttributes( RangeCategoryOfHomomorphismStructure( cat_1 ), Cardinality, BigInt( 1 ) );
end
########
        
    , 101 : IsPrecompiledDerivation := true );
    
    ##
    AddHomomorphismStructureOnMorphisms( cat,
        
########
function ( cat_1, alpha_1, beta_1 )
    local hoisted_1_1, hoisted_3_1, hoisted_5_1, hoisted_6_1, deduped_9_1, deduped_10_1, deduped_11_1, deduped_12_1, deduped_13_1, deduped_14_1, deduped_15_1, deduped_16_1;
    deduped_16_1 := RepresentativesOfSubgroupsUpToConjugation( cat_1 );
    deduped_15_1 := UnderlyingGroup( cat_1 );
    deduped_14_1 := RangeCategoryOfHomomorphismStructure( cat_1 );
    deduped_13_1 := OneImmutable( deduped_15_1 );
    deduped_12_1 := deduped_16_1[ObjectNumber( Range( beta_1 ) )];
    deduped_11_1 := deduped_16_1[ObjectNumber( Source( beta_1 ) )];
    hoisted_3_1 := deduped_16_1[ObjectNumber( Source( alpha_1 ) )];
    deduped_10_1 := Filtered( List( RightTransversal( deduped_15_1, deduped_12_1 ), InverseImmutable ), function ( g_2 )
            return IsSubset( deduped_12_1, ConjugateSubgroup( hoisted_3_1, g_2 ) );
        end );
    hoisted_1_1 := deduped_16_1[ObjectNumber( Range( alpha_1 ) )];
    deduped_9_1 := Filtered( List( RightTransversal( deduped_15_1, deduped_11_1 ), InverseImmutable ), function ( g_2 )
            return IsSubset( deduped_11_1, ConjugateSubgroup( hoisted_1_1, g_2 ) );
        end );
    hoisted_6_1 := UnderlyingGroupElement( beta_1 );
    hoisted_5_1 := MultiplyGroupElements( deduped_13_1, UnderlyingGroupElement( alpha_1 ) );
    return CreateCapCategoryMorphismWithAttributes( deduped_14_1, CreateCapCategoryObjectWithAttributes( deduped_14_1, Cardinality, BigInt( Length( deduped_9_1 ) ) ), CreateCapCategoryObjectWithAttributes( deduped_14_1, Cardinality, BigInt( Length( deduped_10_1 ) ) ), AsList, List( deduped_9_1, function ( g_2 )
              local hoisted_1_2;
              hoisted_1_2 := MultiplyGroupElements( MultiplyGroupElements( MultiplyGroupElements( hoisted_5_1, g_2 ), hoisted_6_1 ), deduped_13_1 );
              return -1 + BigInt( SafeUniquePositionProperty( deduped_10_1, function ( g_3 )
                          return MultiplyGroupElements( InverseImmutable( g_3 ), hoisted_1_2 ) in deduped_12_1;
                      end ) );
          end ) );
end
########
        
    , 2708 : IsPrecompiledDerivation := true );
    
    ##
    AddHomomorphismStructureOnMorphismsWithGivenObjects( cat,
        
########
function ( cat_1, source_1, alpha_1, beta_1, range_1 )
    local hoisted_1_1, hoisted_3_1, hoisted_5_1, hoisted_6_1, hoisted_8_1, deduped_9_1, deduped_10_1, deduped_11_1, deduped_12_1, deduped_13_1;
    deduped_13_1 := RepresentativesOfSubgroupsUpToConjugation( cat_1 );
    deduped_12_1 := UnderlyingGroup( cat_1 );
    deduped_11_1 := OneImmutable( deduped_12_1 );
    deduped_10_1 := deduped_13_1[ObjectNumber( Target( beta_1 ) )];
    deduped_9_1 := deduped_13_1[ObjectNumber( Source( beta_1 ) )];
    hoisted_3_1 := deduped_13_1[ObjectNumber( Source( alpha_1 ) )];
    hoisted_8_1 := Filtered( List( RightTransversal( deduped_12_1, deduped_10_1 ), InverseImmutable ), function ( g_2 )
            return IsSubset( deduped_10_1, ConjugateSubgroup( hoisted_3_1, g_2 ) );
        end );
    hoisted_6_1 := UnderlyingGroupElement( beta_1 );
    hoisted_5_1 := MultiplyGroupElements( deduped_11_1, UnderlyingGroupElement( alpha_1 ) );
    hoisted_1_1 := deduped_13_1[ObjectNumber( Target( alpha_1 ) )];
    return CreateCapCategoryMorphismWithAttributes( RangeCategoryOfHomomorphismStructure( cat_1 ), source_1, range_1, AsList, List( Filtered( List( RightTransversal( deduped_12_1, deduped_9_1 ), InverseImmutable ), function ( g_2 )
                return IsSubset( deduped_9_1, ConjugateSubgroup( hoisted_1_1, g_2 ) );
            end ), function ( g_2 )
              local hoisted_1_2;
              hoisted_1_2 := MultiplyGroupElements( MultiplyGroupElements( MultiplyGroupElements( hoisted_5_1, g_2 ), hoisted_6_1 ), deduped_11_1 );
              return -1 + BigInt( SafeUniquePositionProperty( hoisted_8_1, function ( g_3 )
                          return MultiplyGroupElements( InverseImmutable( g_3 ), hoisted_1_2 ) in deduped_10_1;
                      end ) );
          end ) );
end
########
        
    , 2305 : IsPrecompiledDerivation := true );
    
    ##
    AddHomomorphismStructureOnObjects( cat,
        
########
function ( cat_1, arg2_1, arg3_1 )
    local hoisted_1_1, deduped_3_1, deduped_4_1;
    deduped_4_1 := RepresentativesOfSubgroupsUpToConjugation( cat_1 );
    deduped_3_1 := deduped_4_1[ObjectNumber( arg3_1 )];
    hoisted_1_1 := deduped_4_1[ObjectNumber( arg2_1 )];
    return CreateCapCategoryObjectWithAttributes( RangeCategoryOfHomomorphismStructure( cat_1 ), Cardinality, BigInt( Length( Filtered( List( RightTransversal( UnderlyingGroup( cat_1 ), deduped_3_1 ), InverseImmutable ), function ( g_2 )
                  return IsSubset( deduped_3_1, ConjugateSubgroup( hoisted_1_1, g_2 ) );
              end ) ) ) );
end
########
        
    , 201 : IsPrecompiledDerivation := true );
    
    ##
    AddIdentityMorphism( cat,
        
########
function ( cat_1, a_1 )
    return CreateCapCategoryMorphismWithAttributes( cat_1, a_1, a_1, UnderlyingGroupElement, OneImmutable( UnderlyingGroup( cat_1 ) ) );
end
########
        
    , 100 );
    
    ##
    AddInjectiveColift( cat,
        
########
function ( cat_1, alpha_1, beta_1 )
    return CreateCapCategoryMorphismWithAttributes( cat_1, Range( alpha_1 ), Range( beta_1 ), UnderlyingGroupElement, MultiplyGroupElements( InverseImmutable( UnderlyingGroupElement( alpha_1 ) ), UnderlyingGroupElement( beta_1 ) ) );
end
########
        
    , 101 : IsPrecompiledDerivation := true );
    
    ##
    AddInterpretMorphismAsMorphismFromDistinguishedObjectToHomomorphismStructure( cat,
        
########
function ( cat_1, alpha_1 )
    local hoisted_1_1, hoisted_3_1, deduped_4_1, deduped_5_1, deduped_6_1, deduped_7_1;
    deduped_7_1 := RepresentativesOfSubgroupsUpToConjugation( cat_1 );
    deduped_6_1 := RangeCategoryOfHomomorphismStructure( cat_1 );
    deduped_5_1 := deduped_7_1[ObjectNumber( Range( alpha_1 ) )];
    hoisted_1_1 := deduped_7_1[ObjectNumber( Source( alpha_1 ) )];
    deduped_4_1 := Filtered( List( RightTransversal( UnderlyingGroup( cat_1 ), deduped_5_1 ), InverseImmutable ), function ( g_2 )
            return IsSubset( deduped_5_1, ConjugateSubgroup( hoisted_1_1, g_2 ) );
        end );
    hoisted_3_1 := UnderlyingGroupElement( alpha_1 );
    return CreateCapCategoryMorphismWithAttributes( deduped_6_1, CreateCapCategoryObjectWithAttributes( deduped_6_1, Cardinality, BigInt( 1 ) ), CreateCapCategoryObjectWithAttributes( deduped_6_1, Cardinality, BigInt( Length( deduped_4_1 ) ) ), AsList, [ -1 + BigInt( SafeUniquePositionProperty( deduped_4_1, function ( g_2 )
                      return MultiplyGroupElements( InverseImmutable( g_2 ), hoisted_3_1 ) in deduped_5_1;
                  end ) ) ] );
end
########
        
    , 704 : IsPrecompiledDerivation := true );
    
    ##
    AddInterpretMorphismAsMorphismFromDistinguishedObjectToHomomorphismStructureWithGivenObjects( cat,
        
########
function ( cat_1, source_1, alpha_1, range_1 )
    local hoisted_1_1, hoisted_3_1, deduped_4_1, deduped_5_1;
    deduped_5_1 := RepresentativesOfSubgroupsUpToConjugation( cat_1 );
    deduped_4_1 := deduped_5_1[ObjectNumber( Target( alpha_1 ) )];
    hoisted_3_1 := UnderlyingGroupElement( alpha_1 );
    hoisted_1_1 := deduped_5_1[ObjectNumber( Source( alpha_1 ) )];
    return CreateCapCategoryMorphismWithAttributes( RangeCategoryOfHomomorphismStructure( cat_1 ), source_1, range_1, AsList, [ -1 + BigInt( SafeUniquePositionProperty( Filtered( List( RightTransversal( UnderlyingGroup( cat_1 ), deduped_4_1 ), InverseImmutable ), function ( g_2 )
                        return IsSubset( deduped_4_1, ConjugateSubgroup( hoisted_1_1, g_2 ) );
                    end ), function ( g_2 )
                      return MultiplyGroupElements( InverseImmutable( g_2 ), hoisted_3_1 ) in deduped_4_1;
                  end ) ) ] );
end
########
        
    , 401 : IsPrecompiledDerivation := true );
    
    ##
    AddInterpretMorphismFromDistinguishedObjectToHomomorphismStructureAsMorphism( cat,
        
########
function ( cat_1, source_1, range_1, alpha_1 )
    local hoisted_1_1, deduped_3_1, deduped_4_1;
    deduped_4_1 := RepresentativesOfSubgroupsUpToConjugation( cat_1 );
    deduped_3_1 := deduped_4_1[ObjectNumber( range_1 )];
    hoisted_1_1 := deduped_4_1[ObjectNumber( source_1 )];
    return CAP_JIT_INCOMPLETE_LOGIC( CreateCapCategoryMorphismWithAttributes( cat_1, source_1, range_1, UnderlyingGroupElement, CAP_JIT_INCOMPLETE_LOGIC( Filtered( List( RightTransversal( UnderlyingGroup( cat_1 ), deduped_3_1 ), InverseImmutable ), function ( g_2 )
                    return IsSubset( deduped_3_1, ConjugateSubgroup( hoisted_1_1, g_2 ) );
                end )[1 + AsList( alpha_1 )[1]] ) ) );
end
########
        
    , 805 : IsPrecompiledDerivation := true );
    
    ##
    cat!.cached_precompiled_functions.InterpretMorphismFromDistinguishedObjectToHomomorphismStructureAsMorphism :=
        
########
function ( cat_1, source_1, range_1, alpha_1 )
    local hoisted_1_1, deduped_3_1, deduped_4_1;
    deduped_4_1 := RepresentativesOfSubgroupsUpToConjugation( cat_1 );
    deduped_3_1 := deduped_4_1[ObjectNumber( range_1 )];
    hoisted_1_1 := deduped_4_1[ObjectNumber( source_1 )];
    return List( Filtered( List( RightTransversal( UnderlyingGroup( cat_1 ), deduped_3_1 ), InverseImmutable ), function ( g_2 )
                return IsSubset( deduped_3_1, ConjugateSubgroup( hoisted_1_1, g_2 ) );
            end ), function ( g_2 )
              return CreateCapCategoryMorphismWithAttributes( cat_1, source_1, range_1, UnderlyingGroupElement, g_2 );
          end )[1 + AsList( alpha_1 )[1]];
end
########
        
    ;
    
    ##
    AddInverseForMorphisms( cat,
        
########
function ( cat_1, alpha_1 )
    return CreateCapCategoryMorphismWithAttributes( cat_1, Range( alpha_1 ), Source( alpha_1 ), UnderlyingGroupElement, MultiplyGroupElements( OneImmutable( UnderlyingGroup( cat_1 ) ), InverseImmutable( UnderlyingGroupElement( alpha_1 ) ) ) );
end
########
        
    , 202 : IsPrecompiledDerivation := true );
    
    ##
    AddIsAutomorphism( cat,
        
########
function ( cat_1, arg2_1 )
    local deduped_1_1;
    deduped_1_1 := ObjectNumber( Source( arg2_1 ) ) = ObjectNumber( Range( arg2_1 ) );
    return deduped_1_1 and deduped_1_1;
end
########
        
    , 202 : IsPrecompiledDerivation := true );
    
    ##
    AddIsCodominating( cat,
        
########
function ( cat_1, arg2_1, arg3_1 )
    local deduped_1_1;
    deduped_1_1 := RepresentativesOfSubgroupsUpToConjugation( cat_1 );
    return IsSubset( deduped_1_1[ObjectNumber( Range( arg2_1 ) )], ConjugateSubgroup( deduped_1_1[ObjectNumber( Range( arg3_1 ) )], MultiplyGroupElements( InverseImmutable( UnderlyingGroupElement( arg3_1 ) ), UnderlyingGroupElement( arg2_1 ) ) ) );
end
########
        
    , 102 : IsPrecompiledDerivation := true );
    
    ##
    AddIsColiftable( cat,
        
########
function ( cat_1, arg2_1, arg3_1 )
    local deduped_1_1;
    deduped_1_1 := RepresentativesOfSubgroupsUpToConjugation( cat_1 );
    return IsSubset( deduped_1_1[ObjectNumber( Range( arg3_1 ) )], ConjugateSubgroup( deduped_1_1[ObjectNumber( Range( arg2_1 ) )], MultiplyGroupElements( InverseImmutable( UnderlyingGroupElement( arg2_1 ) ), UnderlyingGroupElement( arg3_1 ) ) ) );
end
########
        
    , 100 );
    
    ##
    AddIsColiftableAlongEpimorphism( cat,
        
########
function ( cat_1, arg2_1, arg3_1 )
    local deduped_1_1;
    deduped_1_1 := RepresentativesOfSubgroupsUpToConjugation( cat_1 );
    return IsSubset( deduped_1_1[ObjectNumber( Range( arg3_1 ) )], ConjugateSubgroup( deduped_1_1[ObjectNumber( Range( arg2_1 ) )], MultiplyGroupElements( InverseImmutable( UnderlyingGroupElement( arg2_1 ) ), UnderlyingGroupElement( arg3_1 ) ) ) );
end
########
        
    , 101 : IsPrecompiledDerivation := true );
    
    ##
    AddIsCongruentForMorphisms( cat,
        
########
function ( cat_1, arg2_1, arg3_1 )
    return MultiplyGroupElements( InverseImmutable( UnderlyingGroupElement( arg2_1 ) ), UnderlyingGroupElement( arg3_1 ) ) in RepresentativesOfSubgroupsUpToConjugation( cat_1 )[ObjectNumber( Range( arg2_1 ) )];
end
########
        
    , 100 );
    
    ##
    AddIsDominating( cat,
        
########
function ( cat_1, arg2_1, arg3_1 )
    local deduped_1_1;
    deduped_1_1 := RepresentativesOfSubgroupsUpToConjugation( cat_1 );
    return IsSubset( deduped_1_1[ObjectNumber( Source( arg3_1 ) )], ConjugateSubgroup( deduped_1_1[ObjectNumber( Source( arg2_1 ) )], MultiplyGroupElements( UnderlyingGroupElement( arg2_1 ), InverseImmutable( UnderlyingGroupElement( arg3_1 ) ) ) ) );
end
########
        
    , 102 : IsPrecompiledDerivation := true );
    
    ##
    AddIsEndomorphism( cat,
        
########
function ( cat_1, arg2_1 )
    return ObjectNumber( Source( arg2_1 ) ) = ObjectNumber( Range( arg2_1 ) );
end
########
        
    , 101 : IsPrecompiledDerivation := true );
    
    ##
    AddIsEpimorphism( cat,
        
########
function ( cat_1, arg2_1 )
    return true;
end
########
        
    , 100 );
    
    ##
    AddIsEqualAsFactorobjects( cat,
        
########
function ( cat_1, arg2_1, arg3_1 )
    local deduped_1_1, deduped_2_1, deduped_3_1, deduped_4_1, deduped_5_1;
    deduped_5_1 := UnderlyingGroupElement( arg2_1 );
    deduped_4_1 := UnderlyingGroupElement( arg3_1 );
    deduped_3_1 := RepresentativesOfSubgroupsUpToConjugation( cat_1 );
    deduped_2_1 := deduped_3_1[ObjectNumber( Range( arg3_1 ) )];
    deduped_1_1 := deduped_3_1[ObjectNumber( Range( arg2_1 ) )];
    return IsSubset( deduped_1_1, ConjugateSubgroup( deduped_2_1, MultiplyGroupElements( InverseImmutable( deduped_4_1 ), deduped_5_1 ) ) ) and IsSubset( deduped_2_1, ConjugateSubgroup( deduped_1_1, MultiplyGroupElements( InverseImmutable( deduped_5_1 ), deduped_4_1 ) ) );
end
########
        
    , 205 : IsPrecompiledDerivation := true );
    
    ##
    AddIsEqualAsSubobjects( cat,
        
########
function ( cat_1, arg2_1, arg3_1 )
    local deduped_1_1, deduped_2_1, deduped_3_1, deduped_4_1, deduped_5_1;
    deduped_5_1 := UnderlyingGroupElement( arg3_1 );
    deduped_4_1 := UnderlyingGroupElement( arg2_1 );
    deduped_3_1 := RepresentativesOfSubgroupsUpToConjugation( cat_1 );
    deduped_2_1 := deduped_3_1[ObjectNumber( Source( arg2_1 ) )];
    deduped_1_1 := deduped_3_1[ObjectNumber( Source( arg3_1 ) )];
    return IsSubset( deduped_1_1, ConjugateSubgroup( deduped_2_1, MultiplyGroupElements( deduped_4_1, InverseImmutable( deduped_5_1 ) ) ) ) and IsSubset( deduped_2_1, ConjugateSubgroup( deduped_1_1, MultiplyGroupElements( deduped_5_1, InverseImmutable( deduped_4_1 ) ) ) );
end
########
        
    , 205 : IsPrecompiledDerivation := true );
    
    ##
    AddIsEqualForMorphisms( cat,
        
########
function ( cat_1, arg2_1, arg3_1 )
    return UnderlyingGroupElement( arg2_1 ) = UnderlyingGroupElement( arg3_1 );
end
########
        
    , 100 );
    
    ##
    AddIsEqualForMorphismsOnMor( cat,
        
########
function ( cat_1, arg2_1, arg3_1 )
    if ObjectNumber( Source( arg2_1 ) ) = ObjectNumber( Source( arg3_1 ) ) and ObjectNumber( Range( arg2_1 ) ) = ObjectNumber( Range( arg3_1 ) ) then
        return UnderlyingGroupElement( arg2_1 ) = UnderlyingGroupElement( arg3_1 );
    else
        return false;
    fi;
    return;
end
########
        
    , 301 : IsPrecompiledDerivation := true );
    
    ##
    AddIsEqualForObjects( cat,
        
########
function ( cat_1, arg2_1, arg3_1 )
    return ObjectNumber( arg2_1 ) = ObjectNumber( arg3_1 );
end
########
        
    , 100 );
    
    ##
    AddIsEqualToIdentityMorphism( cat,
        
########
function ( cat_1, arg2_1 )
    if true and ObjectNumber( Range( arg2_1 ) ) = ObjectNumber( Source( arg2_1 ) ) then
        return UnderlyingGroupElement( arg2_1 ) = OneImmutable( UnderlyingGroup( cat_1 ) );
    else
        return false;
    fi;
    return;
end
########
        
    , 402 : IsPrecompiledDerivation := true );
    
    ##
    AddIsHomSetInhabited( cat,
        
########
function ( cat_1, arg2_1, arg3_1 )
    local hoisted_2_1, deduped_3_1, deduped_4_1;
    deduped_4_1 := RepresentativesOfSubgroupsUpToConjugation( cat_1 );
    deduped_3_1 := deduped_4_1[ObjectNumber( arg3_1 )];
    hoisted_2_1 := deduped_4_1[ObjectNumber( arg2_1 )];
    return ForAny( List( RightTransversal( UnderlyingGroup( cat_1 ), deduped_3_1 ), InverseImmutable ), function ( g_2 )
            return IsSubset( ConjugateSubgroup( deduped_3_1, InverseImmutable( g_2 ) ), hoisted_2_1 );
        end );
end
########
        
    , 100 );
    
    ##
    AddIsIdempotent( cat,
        
########
function ( cat_1, arg2_1 )
    local deduped_1_1;
    deduped_1_1 := UnderlyingGroupElement( arg2_1 );
    return MultiplyGroupElements( InverseImmutable( MultiplyGroupElements( deduped_1_1, deduped_1_1 ) ), deduped_1_1 ) in RepresentativesOfSubgroupsUpToConjugation( cat_1 )[ObjectNumber( Range( arg2_1 ) )];
end
########
        
    , 201 : IsPrecompiledDerivation := true );
    
    ##
    AddIsIsomorphicForObjects( cat,
        
########
function ( cat_1, object_1_1, object_2_1 )
    return ObjectNumber( object_1_1 ) = ObjectNumber( object_2_1 );
end
########
        
    , 101 : IsPrecompiledDerivation := true );
    
    ##
    AddIsIsomorphism( cat,
        
########
function ( cat_1, arg2_1 )
    return ObjectNumber( Source( arg2_1 ) ) = ObjectNumber( Range( arg2_1 ) );
end
########
        
    , 100 );
    
    ##
    AddIsLiftable( cat,
        
########
function ( cat_1, arg2_1, arg3_1 )
    local deduped_1_1;
    deduped_1_1 := RepresentativesOfSubgroupsUpToConjugation( cat_1 );
    return IsSubset( deduped_1_1[ObjectNumber( Source( arg3_1 ) )], ConjugateSubgroup( deduped_1_1[ObjectNumber( Source( arg2_1 ) )], MultiplyGroupElements( UnderlyingGroupElement( arg2_1 ), InverseImmutable( UnderlyingGroupElement( arg3_1 ) ) ) ) );
end
########
        
    , 100 );
    
    ##
    AddIsLiftableAlongMonomorphism( cat,
        
########
function ( cat_1, arg2_1, arg3_1 )
    local deduped_1_1;
    deduped_1_1 := RepresentativesOfSubgroupsUpToConjugation( cat_1 );
    return IsSubset( deduped_1_1[ObjectNumber( Source( arg2_1 ) )], ConjugateSubgroup( deduped_1_1[ObjectNumber( Source( arg3_1 ) )], MultiplyGroupElements( UnderlyingGroupElement( arg3_1 ), InverseImmutable( UnderlyingGroupElement( arg2_1 ) ) ) ) );
end
########
        
    , 101 : IsPrecompiledDerivation := true );
    
    ##
    AddIsMonomorphism( cat,
        
########
function ( cat_1, arg2_1 )
    return ObjectNumber( Source( arg2_1 ) ) = ObjectNumber( Range( arg2_1 ) );
end
########
        
    , 100 );
    
    ##
    AddIsOne( cat,
        
########
function ( cat_1, arg2_1 )
    return MultiplyGroupElements( InverseImmutable( OneImmutable( UnderlyingGroup( cat_1 ) ) ), UnderlyingGroupElement( arg2_1 ) ) in RepresentativesOfSubgroupsUpToConjugation( cat_1 )[ObjectNumber( Source( arg2_1 ) )];
end
########
        
    , 201 : IsPrecompiledDerivation := true );
    
    ##
    AddIsSplitEpimorphism( cat,
        
########
function ( cat_1, arg2_1 )
    local deduped_1_1;
    deduped_1_1 := RepresentativesOfSubgroupsUpToConjugation( cat_1 );
    return IsSubset( deduped_1_1[ObjectNumber( Source( arg2_1 ) )], ConjugateSubgroup( deduped_1_1[ObjectNumber( Range( arg2_1 ) )], MultiplyGroupElements( OneImmutable( UnderlyingGroup( cat_1 ) ), InverseImmutable( UnderlyingGroupElement( arg2_1 ) ) ) ) );
end
########
        
    , 201 : IsPrecompiledDerivation := true );
    
    ##
    AddIsSplitMonomorphism( cat,
        
########
function ( cat_1, arg2_1 )
    local deduped_1_1;
    deduped_1_1 := RepresentativesOfSubgroupsUpToConjugation( cat_1 );
    return IsSubset( deduped_1_1[ObjectNumber( Source( arg2_1 ) )], ConjugateSubgroup( deduped_1_1[ObjectNumber( Range( arg2_1 ) )], MultiplyGroupElements( InverseImmutable( UnderlyingGroupElement( arg2_1 ) ), OneImmutable( UnderlyingGroup( cat_1 ) ) ) ) );
end
########
        
    , 201 : IsPrecompiledDerivation := true );
    
    ##
    AddIsTerminal( cat,
        
########
function ( cat_1, arg2_1 )
    return ObjectNumber( arg2_1 ) = NumberOfObjects( cat_1 );
end
########
        
    , 302 : IsPrecompiledDerivation := true );
    
    ##
    AddIsWellDefinedForMorphisms( cat,
        
########
function ( cat_1, alpha_1 )
    local deduped_1_1, deduped_2_1;
    deduped_2_1 := RepresentativesOfSubgroupsUpToConjugation( cat_1 );
    deduped_1_1 := UnderlyingGroupElement( alpha_1 );
    return deduped_1_1 in UnderlyingGroup( cat_1 ) and IsSubset( deduped_2_1[ObjectNumber( Range( alpha_1 ) )], ConjugateSubgroup( deduped_2_1[ObjectNumber( Source( alpha_1 ) )], deduped_1_1 ) );
end
########
        
    , 100 );
    
    ##
    AddIsWellDefinedForMorphismsWithGivenSourceAndRange( cat,
        
########
function ( cat_1, source_1, alpha_1, range_1 )
    local deduped_1_1, deduped_2_1, deduped_3_1, deduped_4_1;
    deduped_4_1 := RepresentativesOfSubgroupsUpToConjugation( cat_1 );
    deduped_3_1 := UnderlyingGroupElement( alpha_1 );
    deduped_2_1 := ObjectNumber( Source( alpha_1 ) );
    deduped_1_1 := ObjectNumber( Range( alpha_1 ) );
    return deduped_3_1 in UnderlyingGroup( cat_1 ) and IsSubset( deduped_4_1[deduped_1_1], ConjugateSubgroup( deduped_4_1[deduped_2_1], deduped_3_1 ) ) and deduped_2_1 = ObjectNumber( source_1 ) and deduped_1_1 = ObjectNumber( range_1 );
end
########
        
    , 301 : IsPrecompiledDerivation := true );
    
    ##
    AddIsWellDefinedForObjects( cat,
        
########
function ( cat_1, arg2_1 )
    return ObjectNumber( arg2_1 ) in [ 1 .. NumberOfObjects( cat_1 ) ];
end
########
        
    , 100 );
    
    ##
    AddIsomorphismFromCoequalizerOfIdentityAndAutomorphismsToCoequalizer( cat,
        
########
function ( cat_1, Y_1, automorphisms_1 )
    local deduped_1_1, hoisted_2_1, hoisted_6_1, hoisted_8_1, deduped_10_1, deduped_11_1, deduped_12_1, deduped_13_1, deduped_14_1, deduped_15_1, deduped_16_1, deduped_17_1, deduped_18_1, deduped_19_1, deduped_20_1;
    deduped_20_1 := Length( automorphisms_1 );
    deduped_19_1 := RepresentativesOfSubgroupsUpToConjugation( cat_1 );
    deduped_18_1 := UnderlyingGroup( cat_1 );
    deduped_17_1 := [ 1 .. deduped_20_1 ];
    deduped_16_1 := [ 1 .. NumberOfObjects( cat_1 ) ];
    deduped_13_1 := CAP_JIT_INCOMPLETE_LOGIC( GeneratorsOfMagmaWithInverses( CAP_JIT_INCOMPLETE_LOGIC( deduped_19_1[ObjectNumber( Y_1 )] ) ) );
    deduped_12_1 := List( deduped_17_1, function ( i_2 )
            return CAP_JIT_INCOMPLETE_LOGIC( UnderlyingGroupElement( CAP_JIT_INCOMPLETE_LOGIC( automorphisms_1[i_2] ) ) );
        end );
    hoisted_6_1 := List( deduped_17_1, function ( i_2 )
            return CAP_JIT_INCOMPLETE_LOGIC( InverseImmutable( UnderlyingGroupElement( CAP_JIT_INCOMPLETE_LOGIC( automorphisms_1[i_2] ) ) ) );
        end );
    deduped_11_1 := SubmagmaWithInverses( deduped_18_1, Concatenation( deduped_13_1, List( [ 1 .. deduped_20_1 - 1 ], function ( i_2 )
                return MultiplyGroupElements( hoisted_6_1[i_2], deduped_12_1[i_2 + 1] );
            end ) ) );
    hoisted_8_1 := Index( deduped_18_1, deduped_11_1 );
    deduped_1_1 := CardinalitiesOfObjects( cat_1 );
    deduped_15_1 := SafeFirst( Filtered( deduped_16_1, function ( i_2 )
              return deduped_1_1[i_2] = hoisted_8_1;
          end ), function ( c_2 )
            return IsConjugate( deduped_18_1, deduped_11_1, deduped_19_1[c_2] );
        end );
    deduped_10_1 := SubmagmaWithInverses( deduped_18_1, Concatenation( deduped_13_1, deduped_12_1 ) );
    hoisted_2_1 := Index( deduped_18_1, deduped_10_1 );
    deduped_14_1 := SafeFirst( Filtered( deduped_16_1, function ( i_2 )
              return deduped_1_1[i_2] = hoisted_2_1;
          end ), function ( c_2 )
            return IsConjugate( deduped_18_1, deduped_10_1, deduped_19_1[c_2] );
        end );
    return CreateCapCategoryMorphismWithAttributes( cat_1, CreateCapCategoryObjectWithAttributes( cat_1, ObjectNumber, deduped_14_1 ), CreateCapCategoryObjectWithAttributes( cat_1, ObjectNumber, deduped_15_1 ), UnderlyingGroupElement, MultiplyGroupElements( InverseImmutable( RepresentativeAction( deduped_18_1, deduped_10_1, deduped_19_1[deduped_14_1] ) ), RepresentativeAction( deduped_18_1, deduped_11_1, deduped_19_1[deduped_15_1] ) ) );
end
########
        
    , 302 : IsPrecompiledDerivation := true );
    
    ##
    cat!.cached_precompiled_functions.IsomorphismFromCoequalizerOfIdentityAndAutomorphismsToCoequalizer :=
        
########
function ( cat_1, Y_1, automorphisms_1 )
    local deduped_1_1, hoisted_2_1, hoisted_3_1, hoisted_7_1, hoisted_8_1, hoisted_10_1, deduped_12_1, deduped_13_1, deduped_14_1, deduped_15_1, deduped_16_1, deduped_17_1, deduped_18_1, deduped_19_1, deduped_20_1, deduped_21_1, deduped_22_1;
    deduped_22_1 := Length( automorphisms_1 );
    deduped_21_1 := RepresentativesOfSubgroupsUpToConjugation( cat_1 );
    deduped_20_1 := UnderlyingGroup( cat_1 );
    deduped_19_1 := [ 1 .. deduped_22_1 ];
    deduped_18_1 := [ 1 .. NumberOfObjects( cat_1 ) ];
    hoisted_2_1 := List( automorphisms_1, UnderlyingGroupElement );
    deduped_17_1 := List( deduped_19_1, function ( i_2 )
            return hoisted_2_1[i_2];
        end );
    deduped_16_1 := List( deduped_21_1, GeneratorsOfMagmaWithInverses )[ObjectNumber( Y_1 )];
    hoisted_7_1 := List( automorphisms_1, function ( x_2 )
            return InverseImmutable( UnderlyingGroupElement( x_2 ) );
        end );
    hoisted_8_1 := List( deduped_19_1, function ( i_2 )
            return hoisted_7_1[i_2];
        end );
    deduped_12_1 := SubmagmaWithInverses( deduped_20_1, Concatenation( deduped_16_1, List( [ 1 .. deduped_22_1 - 1 ], function ( i_2 )
                return MultiplyGroupElements( hoisted_8_1[i_2], deduped_17_1[i_2 + 1] );
            end ) ) );
    hoisted_10_1 := Index( deduped_20_1, deduped_12_1 );
    deduped_1_1 := CardinalitiesOfObjects( cat_1 );
    deduped_15_1 := SafeFirst( Filtered( deduped_18_1, function ( i_2 )
              return deduped_1_1[i_2] = hoisted_10_1;
          end ), function ( c_2 )
            return IsConjugate( deduped_20_1, deduped_12_1, deduped_21_1[c_2] );
        end );
    deduped_13_1 := SubmagmaWithInverses( deduped_20_1, Concatenation( deduped_16_1, deduped_17_1 ) );
    hoisted_3_1 := Index( deduped_20_1, deduped_13_1 );
    deduped_14_1 := SafeFirst( Filtered( deduped_18_1, function ( i_2 )
              return deduped_1_1[i_2] = hoisted_3_1;
          end ), function ( c_2 )
            return IsConjugate( deduped_20_1, deduped_13_1, deduped_21_1[c_2] );
        end );
    return CreateCapCategoryMorphismWithAttributes( cat_1, CreateCapCategoryObjectWithAttributes( cat_1, ObjectNumber, deduped_14_1 ), CreateCapCategoryObjectWithAttributes( cat_1, ObjectNumber, deduped_15_1 ), UnderlyingGroupElement, MultiplyGroupElements( InverseImmutable( RepresentativeAction( deduped_20_1, deduped_13_1, deduped_21_1[deduped_14_1] ) ), RepresentativeAction( deduped_20_1, deduped_12_1, deduped_21_1[deduped_15_1] ) ) );
end
########
        
    ;
    
    ##
    AddIsomorphismFromCoequalizerToCoequalizerOfIdentityAndAutomorphisms( cat,
        
########
function ( cat_1, Y_1, automorphisms_1 )
    local deduped_1_1, hoisted_2_1, hoisted_4_1, hoisted_8_1, deduped_10_1, deduped_11_1, deduped_12_1, deduped_13_1, deduped_14_1, deduped_15_1, deduped_16_1, deduped_17_1, deduped_18_1, deduped_19_1, deduped_20_1;
    deduped_20_1 := Length( automorphisms_1 );
    deduped_19_1 := RepresentativesOfSubgroupsUpToConjugation( cat_1 );
    deduped_18_1 := UnderlyingGroup( cat_1 );
    deduped_17_1 := [ 1 .. deduped_20_1 ];
    deduped_16_1 := [ 1 .. NumberOfObjects( cat_1 ) ];
    deduped_13_1 := CAP_JIT_INCOMPLETE_LOGIC( GeneratorsOfMagmaWithInverses( CAP_JIT_INCOMPLETE_LOGIC( deduped_19_1[ObjectNumber( Y_1 )] ) ) );
    deduped_12_1 := List( deduped_17_1, function ( i_2 )
            return CAP_JIT_INCOMPLETE_LOGIC( UnderlyingGroupElement( CAP_JIT_INCOMPLETE_LOGIC( automorphisms_1[i_2] ) ) );
        end );
    deduped_10_1 := SubmagmaWithInverses( deduped_18_1, Concatenation( deduped_13_1, deduped_12_1 ) );
    hoisted_8_1 := Index( deduped_18_1, deduped_10_1 );
    deduped_1_1 := CardinalitiesOfObjects( cat_1 );
    deduped_15_1 := SafeFirst( Filtered( deduped_16_1, function ( i_2 )
              return deduped_1_1[i_2] = hoisted_8_1;
          end ), function ( c_2 )
            return IsConjugate( deduped_18_1, deduped_10_1, deduped_19_1[c_2] );
        end );
    hoisted_2_1 := List( deduped_17_1, function ( i_2 )
            return CAP_JIT_INCOMPLETE_LOGIC( InverseImmutable( UnderlyingGroupElement( CAP_JIT_INCOMPLETE_LOGIC( automorphisms_1[i_2] ) ) ) );
        end );
    deduped_11_1 := SubmagmaWithInverses( deduped_18_1, Concatenation( deduped_13_1, List( [ 1 .. deduped_20_1 - 1 ], function ( i_2 )
                return MultiplyGroupElements( hoisted_2_1[i_2], deduped_12_1[i_2 + 1] );
            end ) ) );
    hoisted_4_1 := Index( deduped_18_1, deduped_11_1 );
    deduped_14_1 := SafeFirst( Filtered( deduped_16_1, function ( i_2 )
              return deduped_1_1[i_2] = hoisted_4_1;
          end ), function ( c_2 )
            return IsConjugate( deduped_18_1, deduped_11_1, deduped_19_1[c_2] );
        end );
    return CreateCapCategoryMorphismWithAttributes( cat_1, CreateCapCategoryObjectWithAttributes( cat_1, ObjectNumber, deduped_14_1 ), CreateCapCategoryObjectWithAttributes( cat_1, ObjectNumber, deduped_15_1 ), UnderlyingGroupElement, MultiplyGroupElements( InverseImmutable( RepresentativeAction( deduped_18_1, deduped_11_1, deduped_19_1[deduped_14_1] ) ), RepresentativeAction( deduped_18_1, deduped_10_1, deduped_19_1[deduped_15_1] ) ) );
end
########
        
    , 302 : IsPrecompiledDerivation := true );
    
    ##
    cat!.cached_precompiled_functions.IsomorphismFromCoequalizerToCoequalizerOfIdentityAndAutomorphisms :=
        
########
function ( cat_1, Y_1, automorphisms_1 )
    local deduped_1_1, hoisted_2_1, hoisted_3_1, hoisted_4_1, hoisted_6_1, hoisted_10_1, deduped_12_1, deduped_13_1, deduped_14_1, deduped_15_1, deduped_16_1, deduped_17_1, deduped_18_1, deduped_19_1, deduped_20_1, deduped_21_1, deduped_22_1;
    deduped_22_1 := Length( automorphisms_1 );
    deduped_21_1 := RepresentativesOfSubgroupsUpToConjugation( cat_1 );
    deduped_20_1 := UnderlyingGroup( cat_1 );
    deduped_19_1 := [ 1 .. deduped_22_1 ];
    deduped_18_1 := [ 1 .. NumberOfObjects( cat_1 ) ];
    hoisted_4_1 := List( automorphisms_1, UnderlyingGroupElement );
    deduped_17_1 := List( deduped_19_1, function ( i_2 )
            return hoisted_4_1[i_2];
        end );
    deduped_16_1 := List( deduped_21_1, GeneratorsOfMagmaWithInverses )[ObjectNumber( Y_1 )];
    deduped_13_1 := SubmagmaWithInverses( deduped_20_1, Concatenation( deduped_16_1, deduped_17_1 ) );
    hoisted_10_1 := Index( deduped_20_1, deduped_13_1 );
    deduped_1_1 := CardinalitiesOfObjects( cat_1 );
    deduped_15_1 := SafeFirst( Filtered( deduped_18_1, function ( i_2 )
              return deduped_1_1[i_2] = hoisted_10_1;
          end ), function ( c_2 )
            return IsConjugate( deduped_20_1, deduped_13_1, deduped_21_1[c_2] );
        end );
    hoisted_2_1 := List( automorphisms_1, function ( x_2 )
            return InverseImmutable( UnderlyingGroupElement( x_2 ) );
        end );
    hoisted_3_1 := List( deduped_19_1, function ( i_2 )
            return hoisted_2_1[i_2];
        end );
    deduped_12_1 := SubmagmaWithInverses( deduped_20_1, Concatenation( deduped_16_1, List( [ 1 .. deduped_22_1 - 1 ], function ( i_2 )
                return MultiplyGroupElements( hoisted_3_1[i_2], deduped_17_1[i_2 + 1] );
            end ) ) );
    hoisted_6_1 := Index( deduped_20_1, deduped_12_1 );
    deduped_14_1 := SafeFirst( Filtered( deduped_18_1, function ( i_2 )
              return deduped_1_1[i_2] = hoisted_6_1;
          end ), function ( c_2 )
            return IsConjugate( deduped_20_1, deduped_12_1, deduped_21_1[c_2] );
        end );
    return CreateCapCategoryMorphismWithAttributes( cat_1, CreateCapCategoryObjectWithAttributes( cat_1, ObjectNumber, deduped_14_1 ), CreateCapCategoryObjectWithAttributes( cat_1, ObjectNumber, deduped_15_1 ), UnderlyingGroupElement, MultiplyGroupElements( InverseImmutable( RepresentativeAction( deduped_20_1, deduped_12_1, deduped_21_1[deduped_14_1] ) ), RepresentativeAction( deduped_20_1, deduped_13_1, deduped_21_1[deduped_15_1] ) ) );
end
########
        
    ;
    
    ##
    AddLift( cat,
        
########
function ( cat_1, alpha_1, beta_1 )
    return CreateCapCategoryMorphismWithAttributes( cat_1, Source( alpha_1 ), Source( beta_1 ), UnderlyingGroupElement, MultiplyGroupElements( UnderlyingGroupElement( alpha_1 ), InverseImmutable( UnderlyingGroupElement( beta_1 ) ) ) );
end
########
        
    , 100 );
    
    ##
    AddLiftAlongMonomorphism( cat,
        
########
function ( cat_1, iota_1, tau_1 )
    return CreateCapCategoryMorphismWithAttributes( cat_1, Source( tau_1 ), Source( iota_1 ), UnderlyingGroupElement, MultiplyGroupElements( UnderlyingGroupElement( tau_1 ), InverseImmutable( UnderlyingGroupElement( iota_1 ) ) ) );
end
########
        
    , 101 : IsPrecompiledDerivation := true );
    
    ##
    AddMorphismConstructor( cat,
        
########
function ( cat_1, arg2_1, arg3_1, arg4_1 )
    return CreateCapCategoryMorphismWithAttributes( cat_1, arg2_1, arg4_1, UnderlyingGroupElement, arg3_1 );
end
########
        
    , 100 );
    
    ##
    AddMorphismDatum( cat,
        
########
function ( cat_1, arg2_1 )
    return UnderlyingGroupElement( arg2_1 );
end
########
        
    , 100 );
    
    ##
    AddMorphismFromSourceToCoequalizer( cat,
        
########
function ( cat_1, Y_1, morphisms_1 )
    local hoisted_1_1, hoisted_2_1, hoisted_4_1, hoisted_5_1, deduped_9_1, deduped_10_1, deduped_11_1, deduped_12_1, deduped_13_1, deduped_14_1, deduped_15_1;
    deduped_15_1 := Length( morphisms_1 );
    deduped_14_1 := RepresentativesOfSubgroupsUpToConjugation( cat_1 );
    deduped_13_1 := UnderlyingGroup( cat_1 );
    deduped_12_1 := List( morphisms_1, UnderlyingGroupElement );
    deduped_11_1 := [ 1 .. deduped_15_1 ];
    hoisted_4_1 := List( deduped_11_1, function ( i_2 )
            return deduped_12_1[i_2];
        end );
    hoisted_2_1 := List( deduped_11_1, function ( i_2 )
            return CAP_JIT_INCOMPLETE_LOGIC( InverseImmutable( UnderlyingGroupElement( CAP_JIT_INCOMPLETE_LOGIC( morphisms_1[i_2] ) ) ) );
        end );
    deduped_9_1 := SubmagmaWithInverses( deduped_13_1, Concatenation( CAP_JIT_INCOMPLETE_LOGIC( GeneratorsOfMagmaWithInverses( CAP_JIT_INCOMPLETE_LOGIC( deduped_14_1[ObjectNumber( Y_1 )] ) ) ), List( [ 1 .. deduped_15_1 - 1 ], function ( i_2 )
                return MultiplyGroupElements( hoisted_2_1[i_2], hoisted_4_1[i_2 + 1] );
            end ) ) );
    hoisted_5_1 := Index( deduped_13_1, deduped_9_1 );
    hoisted_1_1 := CardinalitiesOfObjects( cat_1 );
    deduped_10_1 := SafeFirst( Filtered( [ 1 .. NumberOfObjects( cat_1 ) ], function ( i_2 )
              return hoisted_1_1[i_2] = hoisted_5_1;
          end ), function ( c_2 )
            return IsConjugate( deduped_13_1, deduped_9_1, deduped_14_1[c_2] );
        end );
    return CreateCapCategoryMorphismWithAttributes( cat_1, CAP_JIT_INCOMPLETE_LOGIC( Source( CAP_JIT_INCOMPLETE_LOGIC( morphisms_1[1] ) ) ), CreateCapCategoryObjectWithAttributes( cat_1, ObjectNumber, deduped_10_1 ), UnderlyingGroupElement, MultiplyGroupElements( deduped_12_1[1], RepresentativeAction( deduped_13_1, deduped_9_1, deduped_14_1[deduped_10_1] ) ) );
end
########
        
    , 202 : IsPrecompiledDerivation := true );
    
    ##
    cat!.cached_precompiled_functions.MorphismFromSourceToCoequalizer :=
        
########
function ( cat_1, Y_1, morphisms_1 )
    local hoisted_1_1, hoisted_2_1, hoisted_3_1, hoisted_5_1, hoisted_6_1, deduped_10_1, deduped_11_1, deduped_12_1, deduped_13_1, deduped_14_1, deduped_15_1, deduped_16_1;
    deduped_16_1 := Length( morphisms_1 );
    deduped_15_1 := RepresentativesOfSubgroupsUpToConjugation( cat_1 );
    deduped_14_1 := UnderlyingGroup( cat_1 );
    deduped_13_1 := List( morphisms_1, UnderlyingGroupElement );
    deduped_12_1 := [ 1 .. deduped_16_1 ];
    hoisted_5_1 := List( deduped_12_1, function ( i_2 )
            return deduped_13_1[i_2];
        end );
    hoisted_2_1 := List( morphisms_1, function ( x_2 )
            return InverseImmutable( UnderlyingGroupElement( x_2 ) );
        end );
    hoisted_3_1 := List( deduped_12_1, function ( i_2 )
            return hoisted_2_1[i_2];
        end );
    deduped_10_1 := SubmagmaWithInverses( deduped_14_1, Concatenation( List( deduped_15_1, GeneratorsOfMagmaWithInverses )[ObjectNumber( Y_1 )], List( [ 1 .. deduped_16_1 - 1 ], function ( i_2 )
                return MultiplyGroupElements( hoisted_3_1[i_2], hoisted_5_1[i_2 + 1] );
            end ) ) );
    hoisted_6_1 := Index( deduped_14_1, deduped_10_1 );
    hoisted_1_1 := CardinalitiesOfObjects( cat_1 );
    deduped_11_1 := SafeFirst( Filtered( [ 1 .. NumberOfObjects( cat_1 ) ], function ( i_2 )
              return hoisted_1_1[i_2] = hoisted_6_1;
          end ), function ( c_2 )
            return IsConjugate( deduped_14_1, deduped_10_1, deduped_15_1[c_2] );
        end );
    return CreateCapCategoryMorphismWithAttributes( cat_1, List( morphisms_1, Source )[1], CreateCapCategoryObjectWithAttributes( cat_1, ObjectNumber, deduped_11_1 ), UnderlyingGroupElement, MultiplyGroupElements( deduped_13_1[1], RepresentativeAction( deduped_14_1, deduped_10_1, deduped_15_1[deduped_11_1] ) ) );
end
########
        
    ;
    
    ##
    AddMorphismFromSourceToCoequalizerWithGivenCoequalizer( cat,
        
########
function ( cat_1, Y_1, morphisms_1, P_1 )
    local hoisted_1_1, hoisted_2_1, hoisted_4_1, hoisted_5_1, deduped_9_1, deduped_10_1, deduped_11_1, deduped_12_1, deduped_13_1, deduped_14_1, deduped_15_1;
    deduped_15_1 := Length( morphisms_1 );
    deduped_14_1 := RepresentativesOfSubgroupsUpToConjugation( cat_1 );
    deduped_13_1 := UnderlyingGroup( cat_1 );
    deduped_12_1 := List( morphisms_1, UnderlyingGroupElement );
    deduped_11_1 := [ 1 .. deduped_15_1 ];
    hoisted_4_1 := List( deduped_11_1, function ( i_2 )
            return deduped_12_1[i_2];
        end );
    hoisted_2_1 := List( deduped_11_1, function ( i_2 )
            return CAP_JIT_INCOMPLETE_LOGIC( InverseImmutable( UnderlyingGroupElement( CAP_JIT_INCOMPLETE_LOGIC( morphisms_1[i_2] ) ) ) );
        end );
    deduped_9_1 := SubmagmaWithInverses( deduped_13_1, Concatenation( CAP_JIT_INCOMPLETE_LOGIC( GeneratorsOfMagmaWithInverses( CAP_JIT_INCOMPLETE_LOGIC( deduped_14_1[ObjectNumber( Y_1 )] ) ) ), List( [ 1 .. deduped_15_1 - 1 ], function ( i_2 )
                return MultiplyGroupElements( hoisted_2_1[i_2], hoisted_4_1[i_2 + 1] );
            end ) ) );
    hoisted_5_1 := Index( deduped_13_1, deduped_9_1 );
    hoisted_1_1 := CardinalitiesOfObjects( cat_1 );
    deduped_10_1 := SafeFirst( Filtered( [ 1 .. NumberOfObjects( cat_1 ) ], function ( i_2 )
              return hoisted_1_1[i_2] = hoisted_5_1;
          end ), function ( c_2 )
            return IsConjugate( deduped_13_1, deduped_9_1, deduped_14_1[c_2] );
        end );
    return CreateCapCategoryMorphismWithAttributes( cat_1, CAP_JIT_INCOMPLETE_LOGIC( Source( CAP_JIT_INCOMPLETE_LOGIC( morphisms_1[1] ) ) ), CreateCapCategoryObjectWithAttributes( cat_1, ObjectNumber, deduped_10_1 ), UnderlyingGroupElement, MultiplyGroupElements( deduped_12_1[1], RepresentativeAction( deduped_13_1, deduped_9_1, deduped_14_1[deduped_10_1] ) ) );
end
########
        
    , 203 : IsPrecompiledDerivation := true );
    
    ##
    cat!.cached_precompiled_functions.MorphismFromSourceToCoequalizerWithGivenCoequalizer :=
        
########
function ( cat_1, Y_1, morphisms_1, P_1 )
    local hoisted_1_1, hoisted_2_1, hoisted_3_1, hoisted_5_1, hoisted_6_1, deduped_10_1, deduped_11_1, deduped_12_1, deduped_13_1, deduped_14_1, deduped_15_1, deduped_16_1;
    deduped_16_1 := Length( morphisms_1 );
    deduped_15_1 := RepresentativesOfSubgroupsUpToConjugation( cat_1 );
    deduped_14_1 := UnderlyingGroup( cat_1 );
    deduped_13_1 := List( morphisms_1, UnderlyingGroupElement );
    deduped_12_1 := [ 1 .. deduped_16_1 ];
    hoisted_5_1 := List( deduped_12_1, function ( i_2 )
            return deduped_13_1[i_2];
        end );
    hoisted_2_1 := List( morphisms_1, function ( x_2 )
            return InverseImmutable( UnderlyingGroupElement( x_2 ) );
        end );
    hoisted_3_1 := List( deduped_12_1, function ( i_2 )
            return hoisted_2_1[i_2];
        end );
    deduped_10_1 := SubmagmaWithInverses( deduped_14_1, Concatenation( List( deduped_15_1, GeneratorsOfMagmaWithInverses )[ObjectNumber( Y_1 )], List( [ 1 .. deduped_16_1 - 1 ], function ( i_2 )
                return MultiplyGroupElements( hoisted_3_1[i_2], hoisted_5_1[i_2 + 1] );
            end ) ) );
    hoisted_6_1 := Index( deduped_14_1, deduped_10_1 );
    hoisted_1_1 := CardinalitiesOfObjects( cat_1 );
    deduped_11_1 := SafeFirst( Filtered( [ 1 .. NumberOfObjects( cat_1 ) ], function ( i_2 )
              return hoisted_1_1[i_2] = hoisted_6_1;
          end ), function ( c_2 )
            return IsConjugate( deduped_14_1, deduped_10_1, deduped_15_1[c_2] );
        end );
    return CreateCapCategoryMorphismWithAttributes( cat_1, List( morphisms_1, Source )[1], CreateCapCategoryObjectWithAttributes( cat_1, ObjectNumber, deduped_11_1 ), UnderlyingGroupElement, MultiplyGroupElements( deduped_13_1[1], RepresentativeAction( deduped_14_1, deduped_10_1, deduped_15_1[deduped_11_1] ) ) );
end
########
        
    ;
    
    ##
    AddMorphismsOfExternalHom( cat,
        
########
function ( cat_1, arg2_1, arg3_1 )
    local hoisted_1_1, deduped_3_1, deduped_4_1;
    deduped_4_1 := RepresentativesOfSubgroupsUpToConjugation( cat_1 );
    deduped_3_1 := deduped_4_1[ObjectNumber( arg3_1 )];
    hoisted_1_1 := deduped_4_1[ObjectNumber( arg2_1 )];
    return List( Filtered( List( RightTransversal( UnderlyingGroup( cat_1 ), deduped_3_1 ), InverseImmutable ), function ( g_2 )
              return IsSubset( deduped_3_1, ConjugateSubgroup( hoisted_1_1, g_2 ) );
          end ), function ( g_2 )
            return CreateCapCategoryMorphismWithAttributes( cat_1, arg2_1, arg3_1, UnderlyingGroupElement, g_2 );
        end );
end
########
        
    , 100 );
    
    ##
    AddObjectConstructor( cat,
        
########
function ( cat_1, arg2_1 )
    return CreateCapCategoryObjectWithAttributes( cat_1, ObjectNumber, arg2_1 );
end
########
        
    , 100 );
    
    ##
    AddObjectDatum( cat,
        
########
function ( cat_1, arg2_1 )
    return ObjectNumber( arg2_1 );
end
########
        
    , 100 );
    
    ##
    AddPostCompose( cat,
        
########
function ( cat_1, beta_1, alpha_1 )
    return CreateCapCategoryMorphismWithAttributes( cat_1, Source( alpha_1 ), Range( beta_1 ), UnderlyingGroupElement, MultiplyGroupElements( UnderlyingGroupElement( alpha_1 ), UnderlyingGroupElement( beta_1 ) ) );
end
########
        
    , 101 : IsPrecompiledDerivation := true );
    
    ##
    AddPostComposeList( cat,
        
########
function ( cat_1, source_1, list_of_morphisms_1, range_1 )
    local deduped_1_1;
    deduped_1_1 := OneImmutable( UnderlyingGroup( cat_1 ) );
    return CreateCapCategoryMorphismWithAttributes( cat_1, source_1, range_1, UnderlyingGroupElement, Iterated( List( list_of_morphisms_1, UnderlyingGroupElement ), function ( alpha_2, beta_2 )
              return MultiplyGroupElements( beta_2, alpha_2 );
          end, deduped_1_1, deduped_1_1 ) );
end
########
        
    , 403 : IsPrecompiledDerivation := true );
    
    ##
    AddPostInverseForMorphisms( cat,
        
########
function ( cat_1, alpha_1 )
    return CreateCapCategoryMorphismWithAttributes( cat_1, Range( alpha_1 ), Source( alpha_1 ), UnderlyingGroupElement, MultiplyGroupElements( InverseImmutable( UnderlyingGroupElement( alpha_1 ) ), OneImmutable( UnderlyingGroup( cat_1 ) ) ) );
end
########
        
    , 201 : IsPrecompiledDerivation := true );
    
    ##
    AddPreCompose( cat,
        
########
function ( cat_1, alpha_1, beta_1 )
    return CreateCapCategoryMorphismWithAttributes( cat_1, Source( alpha_1 ), Range( beta_1 ), UnderlyingGroupElement, MultiplyGroupElements( UnderlyingGroupElement( alpha_1 ), UnderlyingGroupElement( beta_1 ) ) );
end
########
        
    , 100 );
    
    ##
    AddPreComposeList( cat,
        
########
function ( cat_1, source_1, list_of_morphisms_1, range_1 )
    local deduped_1_1;
    deduped_1_1 := OneImmutable( UnderlyingGroup( cat_1 ) );
    return CreateCapCategoryMorphismWithAttributes( cat_1, source_1, range_1, UnderlyingGroupElement, Iterated( List( list_of_morphisms_1, UnderlyingGroupElement ), function ( alpha_2, beta_2 )
              return MultiplyGroupElements( alpha_2, beta_2 );
          end, deduped_1_1, deduped_1_1 ) );
end
########
        
    , 401 : IsPrecompiledDerivation := true );
    
    ##
    AddPreInverseForMorphisms( cat,
        
########
function ( cat_1, alpha_1 )
    return CreateCapCategoryMorphismWithAttributes( cat_1, Range( alpha_1 ), Source( alpha_1 ), UnderlyingGroupElement, MultiplyGroupElements( OneImmutable( UnderlyingGroup( cat_1 ) ), InverseImmutable( UnderlyingGroupElement( alpha_1 ) ) ) );
end
########
        
    , 201 : IsPrecompiledDerivation := true );
    
    ##
    AddProjectionOntoCoequalizer( cat,
        
########
function ( cat_1, Y_1, morphisms_1 )
    local hoisted_1_1, hoisted_2_1, hoisted_3_1, hoisted_4_1, deduped_8_1, deduped_9_1, deduped_10_1, deduped_11_1, deduped_12_1, deduped_13_1;
    deduped_13_1 := Length( morphisms_1 );
    deduped_12_1 := RepresentativesOfSubgroupsUpToConjugation( cat_1 );
    deduped_11_1 := UnderlyingGroup( cat_1 );
    deduped_10_1 := [ 1 .. deduped_13_1 ];
    hoisted_3_1 := List( deduped_10_1, function ( i_2 )
            return CAP_JIT_INCOMPLETE_LOGIC( UnderlyingGroupElement( CAP_JIT_INCOMPLETE_LOGIC( morphisms_1[i_2] ) ) );
        end );
    hoisted_2_1 := List( deduped_10_1, function ( i_2 )
            return CAP_JIT_INCOMPLETE_LOGIC( InverseImmutable( UnderlyingGroupElement( CAP_JIT_INCOMPLETE_LOGIC( morphisms_1[i_2] ) ) ) );
        end );
    deduped_8_1 := SubmagmaWithInverses( deduped_11_1, Concatenation( CAP_JIT_INCOMPLETE_LOGIC( GeneratorsOfMagmaWithInverses( CAP_JIT_INCOMPLETE_LOGIC( deduped_12_1[ObjectNumber( Y_1 )] ) ) ), List( [ 1 .. deduped_13_1 - 1 ], function ( i_2 )
                return MultiplyGroupElements( hoisted_2_1[i_2], hoisted_3_1[i_2 + 1] );
            end ) ) );
    hoisted_4_1 := Index( deduped_11_1, deduped_8_1 );
    hoisted_1_1 := CardinalitiesOfObjects( cat_1 );
    deduped_9_1 := SafeFirst( Filtered( [ 1 .. NumberOfObjects( cat_1 ) ], function ( i_2 )
              return hoisted_1_1[i_2] = hoisted_4_1;
          end ), function ( c_2 )
            return IsConjugate( deduped_11_1, deduped_8_1, deduped_12_1[c_2] );
        end );
    return CreateCapCategoryMorphismWithAttributes( cat_1, Y_1, CreateCapCategoryObjectWithAttributes( cat_1, ObjectNumber, deduped_9_1 ), UnderlyingGroupElement, RepresentativeAction( deduped_11_1, deduped_8_1, deduped_12_1[deduped_9_1] ) );
end
########
        
    , 100 );
    
    ##
    cat!.cached_precompiled_functions.ProjectionOntoCoequalizer :=
        
########
function ( cat_1, Y_1, morphisms_1 )
    local hoisted_1_1, hoisted_2_1, hoisted_3_1, hoisted_4_1, hoisted_5_1, hoisted_6_1, deduped_10_1, deduped_11_1, deduped_12_1, deduped_13_1, deduped_14_1, deduped_15_1;
    deduped_15_1 := Length( morphisms_1 );
    deduped_14_1 := RepresentativesOfSubgroupsUpToConjugation( cat_1 );
    deduped_13_1 := UnderlyingGroup( cat_1 );
    deduped_12_1 := [ 1 .. deduped_15_1 ];
    hoisted_4_1 := List( morphisms_1, UnderlyingGroupElement );
    hoisted_5_1 := List( deduped_12_1, function ( i_2 )
            return hoisted_4_1[i_2];
        end );
    hoisted_2_1 := List( morphisms_1, function ( x_2 )
            return InverseImmutable( UnderlyingGroupElement( x_2 ) );
        end );
    hoisted_3_1 := List( deduped_12_1, function ( i_2 )
            return hoisted_2_1[i_2];
        end );
    deduped_10_1 := SubmagmaWithInverses( deduped_13_1, Concatenation( List( deduped_14_1, GeneratorsOfMagmaWithInverses )[ObjectNumber( Y_1 )], List( [ 1 .. deduped_15_1 - 1 ], function ( i_2 )
                return MultiplyGroupElements( hoisted_3_1[i_2], hoisted_5_1[i_2 + 1] );
            end ) ) );
    hoisted_6_1 := Index( deduped_13_1, deduped_10_1 );
    hoisted_1_1 := CardinalitiesOfObjects( cat_1 );
    deduped_11_1 := SafeFirst( Filtered( [ 1 .. NumberOfObjects( cat_1 ) ], function ( i_2 )
              return hoisted_1_1[i_2] = hoisted_6_1;
          end ), function ( c_2 )
            return IsConjugate( deduped_13_1, deduped_10_1, deduped_14_1[c_2] );
        end );
    return CreateCapCategoryMorphismWithAttributes( cat_1, Y_1, CreateCapCategoryObjectWithAttributes( cat_1, ObjectNumber, deduped_11_1 ), UnderlyingGroupElement, RepresentativeAction( deduped_13_1, deduped_10_1, deduped_14_1[deduped_11_1] ) );
end
########
        
    ;
    
    ##
    AddProjectionOntoCoequalizerOfIdentityAndAutomorphisms( cat,
        
########
function ( cat_1, Y_1, automorphisms_1 )
    local hoisted_1_1, hoisted_2_1, deduped_6_1, deduped_7_1, deduped_8_1, deduped_9_1;
    deduped_9_1 := RepresentativesOfSubgroupsUpToConjugation( cat_1 );
    deduped_8_1 := UnderlyingGroup( cat_1 );
    deduped_6_1 := SubmagmaWithInverses( deduped_8_1, Concatenation( CAP_JIT_INCOMPLETE_LOGIC( GeneratorsOfMagmaWithInverses( CAP_JIT_INCOMPLETE_LOGIC( deduped_9_1[ObjectNumber( Y_1 )] ) ) ), List( [ 1 .. Length( automorphisms_1 ) ], function ( i_2 )
                return CAP_JIT_INCOMPLETE_LOGIC( UnderlyingGroupElement( CAP_JIT_INCOMPLETE_LOGIC( automorphisms_1[i_2] ) ) );
            end ) ) );
    hoisted_2_1 := Index( deduped_8_1, deduped_6_1 );
    hoisted_1_1 := CardinalitiesOfObjects( cat_1 );
    deduped_7_1 := SafeFirst( Filtered( [ 1 .. NumberOfObjects( cat_1 ) ], function ( i_2 )
              return hoisted_1_1[i_2] = hoisted_2_1;
          end ), function ( c_2 )
            return IsConjugate( deduped_8_1, deduped_6_1, deduped_9_1[c_2] );
        end );
    return CreateCapCategoryMorphismWithAttributes( cat_1, Y_1, CreateCapCategoryObjectWithAttributes( cat_1, ObjectNumber, deduped_7_1 ), UnderlyingGroupElement, RepresentativeAction( deduped_8_1, deduped_6_1, deduped_9_1[deduped_7_1] ) );
end
########
        
    , 100 );
    
    ##
    cat!.cached_precompiled_functions.ProjectionOntoCoequalizerOfIdentityAndAutomorphisms :=
        
########
function ( cat_1, Y_1, automorphisms_1 )
    local hoisted_1_1, hoisted_2_1, hoisted_3_1, deduped_7_1, deduped_8_1, deduped_9_1, deduped_10_1;
    deduped_10_1 := RepresentativesOfSubgroupsUpToConjugation( cat_1 );
    deduped_9_1 := UnderlyingGroup( cat_1 );
    hoisted_2_1 := List( automorphisms_1, UnderlyingGroupElement );
    deduped_7_1 := SubmagmaWithInverses( deduped_9_1, Concatenation( List( deduped_10_1, GeneratorsOfMagmaWithInverses )[ObjectNumber( Y_1 )], List( [ 1 .. Length( automorphisms_1 ) ], function ( i_2 )
                return hoisted_2_1[i_2];
            end ) ) );
    hoisted_3_1 := Index( deduped_9_1, deduped_7_1 );
    hoisted_1_1 := CardinalitiesOfObjects( cat_1 );
    deduped_8_1 := SafeFirst( Filtered( [ 1 .. NumberOfObjects( cat_1 ) ], function ( i_2 )
              return hoisted_1_1[i_2] = hoisted_3_1;
          end ), function ( c_2 )
            return IsConjugate( deduped_9_1, deduped_7_1, deduped_10_1[c_2] );
        end );
    return CreateCapCategoryMorphismWithAttributes( cat_1, Y_1, CreateCapCategoryObjectWithAttributes( cat_1, ObjectNumber, deduped_8_1 ), UnderlyingGroupElement, RepresentativeAction( deduped_9_1, deduped_7_1, deduped_10_1[deduped_8_1] ) );
end
########
        
    ;
    
    ##
    AddProjectionOntoCoequalizerOfIdentityAndAutomorphismsWithGivenCoequalizer( cat,
        
########
function ( cat_1, Y_1, automorphisms_1, P_1 )
    local hoisted_1_1, hoisted_2_1, deduped_6_1, deduped_7_1, deduped_8_1, deduped_9_1;
    deduped_9_1 := RepresentativesOfSubgroupsUpToConjugation( cat_1 );
    deduped_8_1 := UnderlyingGroup( cat_1 );
    deduped_6_1 := SubmagmaWithInverses( deduped_8_1, Concatenation( CAP_JIT_INCOMPLETE_LOGIC( GeneratorsOfMagmaWithInverses( CAP_JIT_INCOMPLETE_LOGIC( deduped_9_1[ObjectNumber( Y_1 )] ) ) ), List( [ 1 .. Length( automorphisms_1 ) ], function ( i_2 )
                return CAP_JIT_INCOMPLETE_LOGIC( UnderlyingGroupElement( CAP_JIT_INCOMPLETE_LOGIC( automorphisms_1[i_2] ) ) );
            end ) ) );
    hoisted_2_1 := Index( deduped_8_1, deduped_6_1 );
    hoisted_1_1 := CardinalitiesOfObjects( cat_1 );
    deduped_7_1 := SafeFirst( Filtered( [ 1 .. NumberOfObjects( cat_1 ) ], function ( i_2 )
              return hoisted_1_1[i_2] = hoisted_2_1;
          end ), function ( c_2 )
            return IsConjugate( deduped_8_1, deduped_6_1, deduped_9_1[c_2] );
        end );
    return CreateCapCategoryMorphismWithAttributes( cat_1, Y_1, CreateCapCategoryObjectWithAttributes( cat_1, ObjectNumber, deduped_7_1 ), UnderlyingGroupElement, RepresentativeAction( deduped_8_1, deduped_6_1, deduped_9_1[deduped_7_1] ) );
end
########
        
    , 101 : IsPrecompiledDerivation := true );
    
    ##
    cat!.cached_precompiled_functions.ProjectionOntoCoequalizerOfIdentityAndAutomorphismsWithGivenCoequalizer :=
        
########
function ( cat_1, Y_1, automorphisms_1, P_1 )
    local hoisted_1_1, hoisted_2_1, hoisted_3_1, deduped_7_1, deduped_8_1, deduped_9_1, deduped_10_1;
    deduped_10_1 := RepresentativesOfSubgroupsUpToConjugation( cat_1 );
    deduped_9_1 := UnderlyingGroup( cat_1 );
    hoisted_2_1 := List( automorphisms_1, UnderlyingGroupElement );
    deduped_7_1 := SubmagmaWithInverses( deduped_9_1, Concatenation( List( deduped_10_1, GeneratorsOfMagmaWithInverses )[ObjectNumber( Y_1 )], List( [ 1 .. Length( automorphisms_1 ) ], function ( i_2 )
                return hoisted_2_1[i_2];
            end ) ) );
    hoisted_3_1 := Index( deduped_9_1, deduped_7_1 );
    hoisted_1_1 := CardinalitiesOfObjects( cat_1 );
    deduped_8_1 := SafeFirst( Filtered( [ 1 .. NumberOfObjects( cat_1 ) ], function ( i_2 )
              return hoisted_1_1[i_2] = hoisted_3_1;
          end ), function ( c_2 )
            return IsConjugate( deduped_9_1, deduped_7_1, deduped_10_1[c_2] );
        end );
    return CreateCapCategoryMorphismWithAttributes( cat_1, Y_1, CreateCapCategoryObjectWithAttributes( cat_1, ObjectNumber, deduped_8_1 ), UnderlyingGroupElement, RepresentativeAction( deduped_9_1, deduped_7_1, deduped_10_1[deduped_8_1] ) );
end
########
        
    ;
    
    ##
    AddProjectionOntoCoequalizerWithGivenCoequalizer( cat,
        
########
function ( cat_1, Y_1, morphisms_1, P_1 )
    local hoisted_1_1, hoisted_2_1, hoisted_3_1, hoisted_4_1, deduped_8_1, deduped_9_1, deduped_10_1, deduped_11_1, deduped_12_1, deduped_13_1;
    deduped_13_1 := Length( morphisms_1 );
    deduped_12_1 := RepresentativesOfSubgroupsUpToConjugation( cat_1 );
    deduped_11_1 := UnderlyingGroup( cat_1 );
    deduped_10_1 := [ 1 .. deduped_13_1 ];
    hoisted_3_1 := List( deduped_10_1, function ( i_2 )
            return CAP_JIT_INCOMPLETE_LOGIC( UnderlyingGroupElement( CAP_JIT_INCOMPLETE_LOGIC( morphisms_1[i_2] ) ) );
        end );
    hoisted_2_1 := List( deduped_10_1, function ( i_2 )
            return CAP_JIT_INCOMPLETE_LOGIC( InverseImmutable( UnderlyingGroupElement( CAP_JIT_INCOMPLETE_LOGIC( morphisms_1[i_2] ) ) ) );
        end );
    deduped_8_1 := SubmagmaWithInverses( deduped_11_1, Concatenation( CAP_JIT_INCOMPLETE_LOGIC( GeneratorsOfMagmaWithInverses( CAP_JIT_INCOMPLETE_LOGIC( deduped_12_1[ObjectNumber( Y_1 )] ) ) ), List( [ 1 .. deduped_13_1 - 1 ], function ( i_2 )
                return MultiplyGroupElements( hoisted_2_1[i_2], hoisted_3_1[i_2 + 1] );
            end ) ) );
    hoisted_4_1 := Index( deduped_11_1, deduped_8_1 );
    hoisted_1_1 := CardinalitiesOfObjects( cat_1 );
    deduped_9_1 := SafeFirst( Filtered( [ 1 .. NumberOfObjects( cat_1 ) ], function ( i_2 )
              return hoisted_1_1[i_2] = hoisted_4_1;
          end ), function ( c_2 )
            return IsConjugate( deduped_11_1, deduped_8_1, deduped_12_1[c_2] );
        end );
    return CreateCapCategoryMorphismWithAttributes( cat_1, Y_1, CreateCapCategoryObjectWithAttributes( cat_1, ObjectNumber, deduped_9_1 ), UnderlyingGroupElement, RepresentativeAction( deduped_11_1, deduped_8_1, deduped_12_1[deduped_9_1] ) );
end
########
        
    , 101 : IsPrecompiledDerivation := true );
    
    ##
    cat!.cached_precompiled_functions.ProjectionOntoCoequalizerWithGivenCoequalizer :=
        
########
function ( cat_1, Y_1, morphisms_1, P_1 )
    local hoisted_1_1, hoisted_2_1, hoisted_3_1, hoisted_4_1, hoisted_5_1, hoisted_6_1, deduped_10_1, deduped_11_1, deduped_12_1, deduped_13_1, deduped_14_1, deduped_15_1;
    deduped_15_1 := Length( morphisms_1 );
    deduped_14_1 := RepresentativesOfSubgroupsUpToConjugation( cat_1 );
    deduped_13_1 := UnderlyingGroup( cat_1 );
    deduped_12_1 := [ 1 .. deduped_15_1 ];
    hoisted_4_1 := List( morphisms_1, UnderlyingGroupElement );
    hoisted_5_1 := List( deduped_12_1, function ( i_2 )
            return hoisted_4_1[i_2];
        end );
    hoisted_2_1 := List( morphisms_1, function ( x_2 )
            return InverseImmutable( UnderlyingGroupElement( x_2 ) );
        end );
    hoisted_3_1 := List( deduped_12_1, function ( i_2 )
            return hoisted_2_1[i_2];
        end );
    deduped_10_1 := SubmagmaWithInverses( deduped_13_1, Concatenation( List( deduped_14_1, GeneratorsOfMagmaWithInverses )[ObjectNumber( Y_1 )], List( [ 1 .. deduped_15_1 - 1 ], function ( i_2 )
                return MultiplyGroupElements( hoisted_3_1[i_2], hoisted_5_1[i_2 + 1] );
            end ) ) );
    hoisted_6_1 := Index( deduped_13_1, deduped_10_1 );
    hoisted_1_1 := CardinalitiesOfObjects( cat_1 );
    deduped_11_1 := SafeFirst( Filtered( [ 1 .. NumberOfObjects( cat_1 ) ], function ( i_2 )
              return hoisted_1_1[i_2] = hoisted_6_1;
          end ), function ( c_2 )
            return IsConjugate( deduped_13_1, deduped_10_1, deduped_14_1[c_2] );
        end );
    return CreateCapCategoryMorphismWithAttributes( cat_1, Y_1, CreateCapCategoryObjectWithAttributes( cat_1, ObjectNumber, deduped_11_1 ), UnderlyingGroupElement, RepresentativeAction( deduped_13_1, deduped_10_1, deduped_14_1[deduped_11_1] ) );
end
########
        
    ;
    
    ##
    AddProjectiveLift( cat,
        
########
function ( cat_1, alpha_1, beta_1 )
    return CreateCapCategoryMorphismWithAttributes( cat_1, Source( alpha_1 ), Source( beta_1 ), UnderlyingGroupElement, MultiplyGroupElements( UnderlyingGroupElement( alpha_1 ), InverseImmutable( UnderlyingGroupElement( beta_1 ) ) ) );
end
########
        
    , 101 : IsPrecompiledDerivation := true );
    
    ##
    AddSetOfMorphismsOfFiniteCategory( cat,
        
########
function ( cat_1 )
    local deduped_1_1, hoisted_2_1, deduped_4_1;
    deduped_4_1 := [ 1 .. NumberOfObjects( cat_1 ) ];
    hoisted_2_1 := UnderlyingGroup( cat_1 );
    deduped_1_1 := RepresentativesOfSubgroupsUpToConjugation( cat_1 );
    return Concatenation( List( deduped_4_1, function ( i_2 )
              local hoisted_2_2, hoisted_3_2, deduped_4_2;
              deduped_4_2 := deduped_1_1[i_2];
              hoisted_3_2 := CreateCapCategoryObjectWithAttributes( cat_1, ObjectNumber, i_2 );
              hoisted_2_2 := List( RightTransversal( hoisted_2_1, deduped_4_2 ), InverseImmutable );
              return Concatenation( List( deduped_4_1, function ( i_3 )
                        local hoisted_1_3, hoisted_2_3;
                        hoisted_2_3 := CreateCapCategoryObjectWithAttributes( cat_1, ObjectNumber, i_3 );
                        hoisted_1_3 := deduped_1_1[i_3];
                        return List( Filtered( hoisted_2_2, function ( g_4 )
                                  return IsSubset( deduped_4_2, ConjugateSubgroup( hoisted_1_3, g_4 ) );
                              end ), function ( g_4 )
                                return CreateCapCategoryMorphismWithAttributes( cat_1, hoisted_2_3, hoisted_3_2, UnderlyingGroupElement, g_4 );
                            end );
                    end ) );
          end ) );
end
########
        
    , 501 : IsPrecompiledDerivation := true );
    
    ##
    AddSetOfObjectsOfCategory( cat,
        
########
function ( cat_1 )
    return List( [ 1 .. NumberOfObjects( cat_1 ) ], function ( i_2 )
            return CreateCapCategoryObjectWithAttributes( cat_1, ObjectNumber, i_2 );
        end );
end
########
        
    , 100 );
    
    ##
    AddSomeIsomorphismBetweenObjects( cat,
        
########
function ( cat_1, object_1_1, object_2_1 )
    return CreateCapCategoryMorphismWithAttributes( cat_1, object_1_1, object_1_1, UnderlyingGroupElement, OneImmutable( UnderlyingGroup( cat_1 ) ) );
end
########
        
    , 101 : IsPrecompiledDerivation := true );
    
    ##
    AddTerminalObject( cat,
        
########
function ( cat_1 )
    return CreateCapCategoryObjectWithAttributes( cat_1, ObjectNumber, NumberOfObjects( cat_1 ) );
end
########
        
    , 100 );
    
    ##
    AddTerminalObjectFunctorial( cat,
        
########
function ( cat_1 )
    local deduped_1_1;
    deduped_1_1 := CreateCapCategoryObjectWithAttributes( cat_1, ObjectNumber, NumberOfObjects( cat_1 ) );
    return CreateCapCategoryMorphismWithAttributes( cat_1, deduped_1_1, deduped_1_1, UnderlyingGroupElement, OneImmutable( UnderlyingGroup( cat_1 ) ) );
end
########
        
    , 201 : IsPrecompiledDerivation := true );
    
    ##
    AddTerminalObjectFunctorialWithGivenTerminalObjects( cat,
        
########
function ( cat_1, P_1, Pp_1 )
    return CreateCapCategoryMorphismWithAttributes( cat_1, P_1, Pp_1, UnderlyingGroupElement, OneImmutable( UnderlyingGroup( cat_1 ) ) );
end
########
        
    , 101 : IsPrecompiledDerivation := true );
    
    ##
    AddUniversalMorphismFromCoequalizer( cat,
        
########
function ( cat_1, Y_1, morphisms_1, T_1, tau_1 )
    local hoisted_1_1, hoisted_2_1, hoisted_3_1, hoisted_4_1, deduped_8_1, deduped_9_1, deduped_10_1, deduped_11_1, deduped_12_1, deduped_13_1;
    deduped_13_1 := Length( morphisms_1 );
    deduped_12_1 := RepresentativesOfSubgroupsUpToConjugation( cat_1 );
    deduped_11_1 := UnderlyingGroup( cat_1 );
    deduped_10_1 := [ 1 .. deduped_13_1 ];
    hoisted_3_1 := List( deduped_10_1, function ( i_2 )
            return CAP_JIT_INCOMPLETE_LOGIC( UnderlyingGroupElement( CAP_JIT_INCOMPLETE_LOGIC( morphisms_1[i_2] ) ) );
        end );
    hoisted_2_1 := List( deduped_10_1, function ( i_2 )
            return CAP_JIT_INCOMPLETE_LOGIC( InverseImmutable( UnderlyingGroupElement( CAP_JIT_INCOMPLETE_LOGIC( morphisms_1[i_2] ) ) ) );
        end );
    deduped_8_1 := SubmagmaWithInverses( deduped_11_1, Concatenation( CAP_JIT_INCOMPLETE_LOGIC( GeneratorsOfMagmaWithInverses( CAP_JIT_INCOMPLETE_LOGIC( deduped_12_1[ObjectNumber( Y_1 )] ) ) ), List( [ 1 .. deduped_13_1 - 1 ], function ( i_2 )
                return MultiplyGroupElements( hoisted_2_1[i_2], hoisted_3_1[i_2 + 1] );
            end ) ) );
    hoisted_4_1 := Index( deduped_11_1, deduped_8_1 );
    hoisted_1_1 := CardinalitiesOfObjects( cat_1 );
    deduped_9_1 := SafeFirst( Filtered( [ 1 .. NumberOfObjects( cat_1 ) ], function ( i_2 )
              return hoisted_1_1[i_2] = hoisted_4_1;
          end ), function ( c_2 )
            return IsConjugate( deduped_11_1, deduped_8_1, deduped_12_1[c_2] );
        end );
    return CreateCapCategoryMorphismWithAttributes( cat_1, CreateCapCategoryObjectWithAttributes( cat_1, ObjectNumber, deduped_9_1 ), Range( tau_1 ), UnderlyingGroupElement, MultiplyGroupElements( InverseImmutable( RepresentativeAction( deduped_11_1, deduped_8_1, deduped_12_1[deduped_9_1] ) ), UnderlyingGroupElement( tau_1 ) ) );
end
########
        
    , 202 : IsPrecompiledDerivation := true );
    
    ##
    cat!.cached_precompiled_functions.UniversalMorphismFromCoequalizer :=
        
########
function ( cat_1, Y_1, morphisms_1, T_1, tau_1 )
    local hoisted_1_1, hoisted_2_1, hoisted_3_1, hoisted_4_1, hoisted_5_1, hoisted_6_1, deduped_10_1, deduped_11_1, deduped_12_1, deduped_13_1, deduped_14_1, deduped_15_1;
    deduped_15_1 := Length( morphisms_1 );
    deduped_14_1 := RepresentativesOfSubgroupsUpToConjugation( cat_1 );
    deduped_13_1 := UnderlyingGroup( cat_1 );
    deduped_12_1 := [ 1 .. deduped_15_1 ];
    hoisted_4_1 := List( morphisms_1, UnderlyingGroupElement );
    hoisted_5_1 := List( deduped_12_1, function ( i_2 )
            return hoisted_4_1[i_2];
        end );
    hoisted_2_1 := List( morphisms_1, function ( x_2 )
            return InverseImmutable( UnderlyingGroupElement( x_2 ) );
        end );
    hoisted_3_1 := List( deduped_12_1, function ( i_2 )
            return hoisted_2_1[i_2];
        end );
    deduped_10_1 := SubmagmaWithInverses( deduped_13_1, Concatenation( List( deduped_14_1, GeneratorsOfMagmaWithInverses )[ObjectNumber( Y_1 )], List( [ 1 .. deduped_15_1 - 1 ], function ( i_2 )
                return MultiplyGroupElements( hoisted_3_1[i_2], hoisted_5_1[i_2 + 1] );
            end ) ) );
    hoisted_6_1 := Index( deduped_13_1, deduped_10_1 );
    hoisted_1_1 := CardinalitiesOfObjects( cat_1 );
    deduped_11_1 := SafeFirst( Filtered( [ 1 .. NumberOfObjects( cat_1 ) ], function ( i_2 )
              return hoisted_1_1[i_2] = hoisted_6_1;
          end ), function ( c_2 )
            return IsConjugate( deduped_13_1, deduped_10_1, deduped_14_1[c_2] );
        end );
    return CreateCapCategoryMorphismWithAttributes( cat_1, CreateCapCategoryObjectWithAttributes( cat_1, ObjectNumber, deduped_11_1 ), Range( tau_1 ), UnderlyingGroupElement, MultiplyGroupElements( InverseImmutable( RepresentativeAction( deduped_13_1, deduped_10_1, deduped_14_1[deduped_11_1] ) ), UnderlyingGroupElement( tau_1 ) ) );
end
########
        
    ;
    
    ##
    AddUniversalMorphismFromCoequalizerOfIdentityAndAutomorphisms( cat,
        
########
function ( cat_1, Y_1, automorphisms_1, T_1, tau_1 )
    local hoisted_1_1, hoisted_2_1, deduped_6_1, deduped_7_1, deduped_8_1, deduped_9_1;
    deduped_9_1 := RepresentativesOfSubgroupsUpToConjugation( cat_1 );
    deduped_8_1 := UnderlyingGroup( cat_1 );
    deduped_6_1 := SubmagmaWithInverses( deduped_8_1, Concatenation( CAP_JIT_INCOMPLETE_LOGIC( GeneratorsOfMagmaWithInverses( CAP_JIT_INCOMPLETE_LOGIC( deduped_9_1[ObjectNumber( Y_1 )] ) ) ), List( [ 1 .. Length( automorphisms_1 ) ], function ( i_2 )
                return CAP_JIT_INCOMPLETE_LOGIC( UnderlyingGroupElement( CAP_JIT_INCOMPLETE_LOGIC( automorphisms_1[i_2] ) ) );
            end ) ) );
    hoisted_2_1 := Index( deduped_8_1, deduped_6_1 );
    hoisted_1_1 := CardinalitiesOfObjects( cat_1 );
    deduped_7_1 := SafeFirst( Filtered( [ 1 .. NumberOfObjects( cat_1 ) ], function ( i_2 )
              return hoisted_1_1[i_2] = hoisted_2_1;
          end ), function ( c_2 )
            return IsConjugate( deduped_8_1, deduped_6_1, deduped_9_1[c_2] );
        end );
    return CreateCapCategoryMorphismWithAttributes( cat_1, CreateCapCategoryObjectWithAttributes( cat_1, ObjectNumber, deduped_7_1 ), Range( tau_1 ), UnderlyingGroupElement, MultiplyGroupElements( InverseImmutable( RepresentativeAction( deduped_8_1, deduped_6_1, deduped_9_1[deduped_7_1] ) ), UnderlyingGroupElement( tau_1 ) ) );
end
########
        
    , 202 : IsPrecompiledDerivation := true );
    
    ##
    cat!.cached_precompiled_functions.UniversalMorphismFromCoequalizerOfIdentityAndAutomorphisms :=
        
########
function ( cat_1, Y_1, automorphisms_1, T_1, tau_1 )
    local hoisted_1_1, hoisted_2_1, hoisted_3_1, deduped_7_1, deduped_8_1, deduped_9_1, deduped_10_1;
    deduped_10_1 := RepresentativesOfSubgroupsUpToConjugation( cat_1 );
    deduped_9_1 := UnderlyingGroup( cat_1 );
    hoisted_2_1 := List( automorphisms_1, UnderlyingGroupElement );
    deduped_7_1 := SubmagmaWithInverses( deduped_9_1, Concatenation( List( deduped_10_1, GeneratorsOfMagmaWithInverses )[ObjectNumber( Y_1 )], List( [ 1 .. Length( automorphisms_1 ) ], function ( i_2 )
                return hoisted_2_1[i_2];
            end ) ) );
    hoisted_3_1 := Index( deduped_9_1, deduped_7_1 );
    hoisted_1_1 := CardinalitiesOfObjects( cat_1 );
    deduped_8_1 := SafeFirst( Filtered( [ 1 .. NumberOfObjects( cat_1 ) ], function ( i_2 )
              return hoisted_1_1[i_2] = hoisted_3_1;
          end ), function ( c_2 )
            return IsConjugate( deduped_9_1, deduped_7_1, deduped_10_1[c_2] );
        end );
    return CreateCapCategoryMorphismWithAttributes( cat_1, CreateCapCategoryObjectWithAttributes( cat_1, ObjectNumber, deduped_8_1 ), Range( tau_1 ), UnderlyingGroupElement, MultiplyGroupElements( InverseImmutable( RepresentativeAction( deduped_9_1, deduped_7_1, deduped_10_1[deduped_8_1] ) ), UnderlyingGroupElement( tau_1 ) ) );
end
########
        
    ;
    
    ##
    AddUniversalMorphismFromCoequalizerOfIdentityAndAutomorphismsWithGivenCoequalizer( cat,
        
########
function ( cat_1, Y_1, automorphisms_1, T_1, tau_1, P_1 )
    local hoisted_1_1, hoisted_2_1, deduped_6_1, deduped_7_1, deduped_8_1, deduped_9_1;
    deduped_9_1 := RepresentativesOfSubgroupsUpToConjugation( cat_1 );
    deduped_8_1 := UnderlyingGroup( cat_1 );
    deduped_6_1 := SubmagmaWithInverses( deduped_8_1, Concatenation( CAP_JIT_INCOMPLETE_LOGIC( GeneratorsOfMagmaWithInverses( CAP_JIT_INCOMPLETE_LOGIC( deduped_9_1[ObjectNumber( Y_1 )] ) ) ), List( [ 1 .. Length( automorphisms_1 ) ], function ( i_2 )
                return CAP_JIT_INCOMPLETE_LOGIC( UnderlyingGroupElement( CAP_JIT_INCOMPLETE_LOGIC( automorphisms_1[i_2] ) ) );
            end ) ) );
    hoisted_2_1 := Index( deduped_8_1, deduped_6_1 );
    hoisted_1_1 := CardinalitiesOfObjects( cat_1 );
    deduped_7_1 := SafeFirst( Filtered( [ 1 .. NumberOfObjects( cat_1 ) ], function ( i_2 )
              return hoisted_1_1[i_2] = hoisted_2_1;
          end ), function ( c_2 )
            return IsConjugate( deduped_8_1, deduped_6_1, deduped_9_1[c_2] );
        end );
    return CreateCapCategoryMorphismWithAttributes( cat_1, CreateCapCategoryObjectWithAttributes( cat_1, ObjectNumber, deduped_7_1 ), Range( tau_1 ), UnderlyingGroupElement, MultiplyGroupElements( InverseImmutable( RepresentativeAction( deduped_8_1, deduped_6_1, deduped_9_1[deduped_7_1] ) ), UnderlyingGroupElement( tau_1 ) ) );
end
########
        
    , 203 : IsPrecompiledDerivation := true );
    
    ##
    cat!.cached_precompiled_functions.UniversalMorphismFromCoequalizerOfIdentityAndAutomorphismsWithGivenCoequalizer :=
        
########
function ( cat_1, Y_1, automorphisms_1, T_1, tau_1, P_1 )
    local hoisted_1_1, hoisted_2_1, hoisted_3_1, deduped_7_1, deduped_8_1, deduped_9_1, deduped_10_1;
    deduped_10_1 := RepresentativesOfSubgroupsUpToConjugation( cat_1 );
    deduped_9_1 := UnderlyingGroup( cat_1 );
    hoisted_2_1 := List( automorphisms_1, UnderlyingGroupElement );
    deduped_7_1 := SubmagmaWithInverses( deduped_9_1, Concatenation( List( deduped_10_1, GeneratorsOfMagmaWithInverses )[ObjectNumber( Y_1 )], List( [ 1 .. Length( automorphisms_1 ) ], function ( i_2 )
                return hoisted_2_1[i_2];
            end ) ) );
    hoisted_3_1 := Index( deduped_9_1, deduped_7_1 );
    hoisted_1_1 := CardinalitiesOfObjects( cat_1 );
    deduped_8_1 := SafeFirst( Filtered( [ 1 .. NumberOfObjects( cat_1 ) ], function ( i_2 )
              return hoisted_1_1[i_2] = hoisted_3_1;
          end ), function ( c_2 )
            return IsConjugate( deduped_9_1, deduped_7_1, deduped_10_1[c_2] );
        end );
    return CreateCapCategoryMorphismWithAttributes( cat_1, CreateCapCategoryObjectWithAttributes( cat_1, ObjectNumber, deduped_8_1 ), Range( tau_1 ), UnderlyingGroupElement, MultiplyGroupElements( InverseImmutable( RepresentativeAction( deduped_9_1, deduped_7_1, deduped_10_1[deduped_8_1] ) ), UnderlyingGroupElement( tau_1 ) ) );
end
########
        
    ;
    
    ##
    AddUniversalMorphismFromCoequalizerWithGivenCoequalizer( cat,
        
########
function ( cat_1, Y_1, morphisms_1, T_1, tau_1, P_1 )
    local hoisted_1_1, hoisted_2_1, hoisted_3_1, hoisted_4_1, deduped_8_1, deduped_9_1, deduped_10_1, deduped_11_1, deduped_12_1, deduped_13_1;
    deduped_13_1 := Length( morphisms_1 );
    deduped_12_1 := RepresentativesOfSubgroupsUpToConjugation( cat_1 );
    deduped_11_1 := UnderlyingGroup( cat_1 );
    deduped_10_1 := [ 1 .. deduped_13_1 ];
    hoisted_3_1 := List( deduped_10_1, function ( i_2 )
            return CAP_JIT_INCOMPLETE_LOGIC( UnderlyingGroupElement( CAP_JIT_INCOMPLETE_LOGIC( morphisms_1[i_2] ) ) );
        end );
    hoisted_2_1 := List( deduped_10_1, function ( i_2 )
            return CAP_JIT_INCOMPLETE_LOGIC( InverseImmutable( UnderlyingGroupElement( CAP_JIT_INCOMPLETE_LOGIC( morphisms_1[i_2] ) ) ) );
        end );
    deduped_8_1 := SubmagmaWithInverses( deduped_11_1, Concatenation( CAP_JIT_INCOMPLETE_LOGIC( GeneratorsOfMagmaWithInverses( CAP_JIT_INCOMPLETE_LOGIC( deduped_12_1[ObjectNumber( Y_1 )] ) ) ), List( [ 1 .. deduped_13_1 - 1 ], function ( i_2 )
                return MultiplyGroupElements( hoisted_2_1[i_2], hoisted_3_1[i_2 + 1] );
            end ) ) );
    hoisted_4_1 := Index( deduped_11_1, deduped_8_1 );
    hoisted_1_1 := CardinalitiesOfObjects( cat_1 );
    deduped_9_1 := SafeFirst( Filtered( [ 1 .. NumberOfObjects( cat_1 ) ], function ( i_2 )
              return hoisted_1_1[i_2] = hoisted_4_1;
          end ), function ( c_2 )
            return IsConjugate( deduped_11_1, deduped_8_1, deduped_12_1[c_2] );
        end );
    return CreateCapCategoryMorphismWithAttributes( cat_1, CreateCapCategoryObjectWithAttributes( cat_1, ObjectNumber, deduped_9_1 ), Range( tau_1 ), UnderlyingGroupElement, MultiplyGroupElements( InverseImmutable( RepresentativeAction( deduped_11_1, deduped_8_1, deduped_12_1[deduped_9_1] ) ), UnderlyingGroupElement( tau_1 ) ) );
end
########
        
    , 203 : IsPrecompiledDerivation := true );
    
    ##
    cat!.cached_precompiled_functions.UniversalMorphismFromCoequalizerWithGivenCoequalizer :=
        
########
function ( cat_1, Y_1, morphisms_1, T_1, tau_1, P_1 )
    local hoisted_1_1, hoisted_2_1, hoisted_3_1, hoisted_4_1, hoisted_5_1, hoisted_6_1, deduped_10_1, deduped_11_1, deduped_12_1, deduped_13_1, deduped_14_1, deduped_15_1;
    deduped_15_1 := Length( morphisms_1 );
    deduped_14_1 := RepresentativesOfSubgroupsUpToConjugation( cat_1 );
    deduped_13_1 := UnderlyingGroup( cat_1 );
    deduped_12_1 := [ 1 .. deduped_15_1 ];
    hoisted_4_1 := List( morphisms_1, UnderlyingGroupElement );
    hoisted_5_1 := List( deduped_12_1, function ( i_2 )
            return hoisted_4_1[i_2];
        end );
    hoisted_2_1 := List( morphisms_1, function ( x_2 )
            return InverseImmutable( UnderlyingGroupElement( x_2 ) );
        end );
    hoisted_3_1 := List( deduped_12_1, function ( i_2 )
            return hoisted_2_1[i_2];
        end );
    deduped_10_1 := SubmagmaWithInverses( deduped_13_1, Concatenation( List( deduped_14_1, GeneratorsOfMagmaWithInverses )[ObjectNumber( Y_1 )], List( [ 1 .. deduped_15_1 - 1 ], function ( i_2 )
                return MultiplyGroupElements( hoisted_3_1[i_2], hoisted_5_1[i_2 + 1] );
            end ) ) );
    hoisted_6_1 := Index( deduped_13_1, deduped_10_1 );
    hoisted_1_1 := CardinalitiesOfObjects( cat_1 );
    deduped_11_1 := SafeFirst( Filtered( [ 1 .. NumberOfObjects( cat_1 ) ], function ( i_2 )
              return hoisted_1_1[i_2] = hoisted_6_1;
          end ), function ( c_2 )
            return IsConjugate( deduped_13_1, deduped_10_1, deduped_14_1[c_2] );
        end );
    return CreateCapCategoryMorphismWithAttributes( cat_1, CreateCapCategoryObjectWithAttributes( cat_1, ObjectNumber, deduped_11_1 ), Range( tau_1 ), UnderlyingGroupElement, MultiplyGroupElements( InverseImmutable( RepresentativeAction( deduped_13_1, deduped_10_1, deduped_14_1[deduped_11_1] ) ), UnderlyingGroupElement( tau_1 ) ) );
end
########
        
    ;
    
    ##
    AddUniversalMorphismIntoTerminalObject( cat,
        
########
function ( cat_1, T_1 )
    return CreateCapCategoryMorphismWithAttributes( cat_1, T_1, CreateCapCategoryObjectWithAttributes( cat_1, ObjectNumber, NumberOfObjects( cat_1 ) ), UnderlyingGroupElement, OneImmutable( UnderlyingGroup( cat_1 ) ) );
end
########
        
    , 201 : IsPrecompiledDerivation := true );
    
    ##
    AddUniversalMorphismIntoTerminalObjectWithGivenTerminalObject( cat,
        
########
function ( cat_1, T_1, P_1 )
    return CreateCapCategoryMorphismWithAttributes( cat_1, T_1, P_1, UnderlyingGroupElement, OneImmutable( UnderlyingGroup( cat_1 ) ) );
end
########
        
    , 100 );
    
    if IsBound( cat!.precompiled_functions_added ) then
        
        # COVERAGE_IGNORE_NEXT_LINE
        Error( "precompiled functions have already been added before" );
        
    fi;
    
    cat!.precompiled_functions_added := true;
    
end );

BindGlobal( "SkeletalCategoryOfTransitiveLeftGSets_precompiled", function ( G )
  local category_constructor, cat;
    
    category_constructor :=
        
        
        function ( G )
    return SkeletalCategoryOfTransitiveLeftGSets( GROUP_AS_CATEGORY( G : FinalizeCategory := true ) );
end;
        
        
    
    cat := category_constructor( G : FinalizeCategory := false, no_precompiled_code := true );
    
    ADD_FUNCTIONS_FOR_SkeletalCategoryOfTransitiveLeftGSets_precompiled( cat );
    
    Finalize( cat );
    
    return cat;
    
end );
