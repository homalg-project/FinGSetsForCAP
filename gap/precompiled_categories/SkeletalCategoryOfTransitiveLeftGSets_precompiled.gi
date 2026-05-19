# SPDX-License-Identifier: GPL-2.0-or-later
# FinGSetsForCAP: The (skeletal) elementary topos of finite G-sets
#
# Implementations
#
BindGlobal( "ADD_FUNCTIONS_FOR_SkeletalCategoryOfTransitiveLeftGSets_precompiled", function ( cat )
    
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
    AddIsEqualForObjects( cat,
        
########
function ( cat_1, arg2_1, arg3_1 )
    return ObjectNumber( arg2_1 ) = ObjectNumber( arg3_1 );
end
########
        
    , 100 );
    
    ##
    AddIsWellDefinedForObjects( cat,
        
########
function ( cat_1, arg2_1 )
    return ObjectNumber( arg2_1 ) in [ 1 .. NumberOfObjects( cat_1 ) ];
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
