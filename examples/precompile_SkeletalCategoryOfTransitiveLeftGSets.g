#! @Chapter Precompilation

#! @Section Precompiling the skeletal category of finite left G-sets

#! @Example

#! #@if ValueOption( "no_precompiled_code" ) <> true

LoadPackage( "FinGSetsForCAP", false );
#! true
LoadPackage( "CompilerForCAP", ">= 2026.05-01", false );
#! true

category_constructor :=
  G -> SkeletalCategoryOfTransitiveLeftGSets(
          GROUP_AS_CATEGORY( G : FinalizeCategory := true ) );;
C2 := CyclicGroup( 2 );; StructureDescription( C2 );; C2;
#! C2
given_arguments := [ C2 ];;
compiled_category_name :=
  "SkeletalCategoryOfTransitiveLeftGSets_precompiled";;
package_name := "FinGSetsForCAP";;
#primitive_operations :=
#  ListPrimitivelyInstalledOperationsOfCategory(
#          category_constructor( given_arguments[1]
#          : no_precompiled_code := true ) );;
list_of_operations :=
  #SortedList( Concatenation( primitive_operations,
          [ "SetOfObjectsOfCategory",
            "IsEqualForObjects",
            "IsWellDefinedForObjects",
            "IsWellDefinedForMorphisms",
            ];;
  #) );;

CapJitPrecompileCategoryAndCompareResult(
        category_constructor,
        given_arguments,
        package_name,
        compiled_category_name
        : operations := list_of_operations,
        number_of_objectified_objects_in_data_structure_of_object := 1,
        number_of_objectified_morphisms_in_data_structure_of_object := 0,
        number_of_objectified_objects_in_data_structure_of_morphism := 2,
        number_of_objectified_morphisms_in_data_structure_of_morphism := 1
);;

SkeletalCategoryOfTransitiveLeftGSets_precompiled( C2 );
#! SkeletalCategoryOfTransitiveLeftGSets( C2 ) with 2 objects

cat := SkeletalCategoryOfTransitiveLeftGSets( C2 );
#! SkeletalCategoryOfTransitiveLeftGSets( C2 ) with 2 objects

cat!.precompiled_functions_added;
#! true

#! #@fi

#! @EndExample
