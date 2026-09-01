/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import Bescovitch.SixPoint.WeightedMixedEqualityLocalCertificate

/-!
# Exact data for the equality mixed chart

This file records two small rational interval trees: one for transverse monotonicity and one
for negative definiteness of the antisymmetric face Hessian.
-/

@[expose] public section

namespace Bescovitch

namespace WeightedMixedEqualityLocal

/-- The rational endpoint box used by the reducible transverse checker. -/
@[reducible]
def exactTransverseRootBox : Fin 9 → RationalInterval := ![
  ⟨1.3866128436518096, 1.3866128436518100, by norm_num⟩,
  ⟨0.08947642540845, 0.08947642540925, by norm_num⟩,
  ⟨0.92883833887503, 0.92883833887577, by norm_num⟩,
  ⟨0.85902, 0.85984, by norm_num⟩,
  ⟨-0.513, 0.513, by norm_num⟩,
  ⟨0.649, 0.655, by norm_num⟩,
  ⟨0.85902, 0.85984, by norm_num⟩,
  ⟨-0.513, 0.513, by norm_num⟩,
  ⟨0.649, 0.655, by norm_num⟩]

/-- The rational endpoint box used by the reducible face checker. -/
@[reducible]
def exactFaceRootBox : Fin 7 → RationalInterval := ![
  ⟨1.3866128436518096, 1.3866128436518100, by norm_num⟩,
  ⟨0.08947642540845, 0.08947642540925, by norm_num⟩,
  ⟨0.92883833887503, 0.92883833887577, by norm_num⟩,
  ⟨0.2745, 0.2754, by norm_num⟩,
  ⟨0.649, 0.655, by norm_num⟩,
  ⟨0.2745, 0.2754, by norm_num⟩,
  ⟨0.649, 0.655, by norm_num⟩]

/-- Exact dyadic norm witnesses for transverse monotonicity. -/
@[reducible]
def transverseCertificateTree : LocalCertificateTree 9 10 :=
  .split 4
    (.split 7
      (.split 4
        (.leaf {
          lowerNumerator := ![2001672179484, 592745101285, 1363027763073, 1285224533386,
            479914941364, 479914941364, 970587140698, 857902567892, 570593471433,
            376021012783]
          widthNumerator := ![728372522774, 449245460663, 286644659239, 563119293360,
            801323903568, 801323903568, 139746073397, 308617288408, 295366976765,
            550097645089]
        })
        (.leaf {
          lowerNumerator := ![2024431736441, 707602628939, 1488935092332, 1285224533386,
            562818974240, 562818974240, 865901307245, 857902567892, 471874231736,
            376021012783]
          widthNumerator := ![777826905248, 536981836778, 293371617512, 563119293360,
            867666400510, 867666400510, 192876705952, 308617288408, 257599280490,
            550097645089]
        }))
      (.leaf {
        lowerNumerator := ![1997242151022, 829403657203, 1285224533386, 1604939952548,
          726764890564, 726764890564, 857902567892, 732827531891, 376021012783,
          526087605952]
        widthNumerator := ![1101253187343, 909970669028, 563119293360, 580746471119,
          1137193263422, 1137193263422, 308617288408, 523481334141, 550097645089,
          290961021319]
      }))
    (.split 7
      (.split 4
        (.split 7
          (.split 4
            (.leaf {
              lowerNumerator := ![2217469132276, 829403657203, 1679872319944, 1363027763073,
                814048521837, 814048521837, 884971723574, 970587140698, 535778324072,
                570593471433]
              widthNumerator := ![415100528379, 305983795633, 154809048571, 286644659239,
                451125150142, 451125150142, 127264753244, 139746073397, 101745507670,
                295366976765]
            })
            (.leaf {
              lowerNumerator := ![2252836157507, 909727066849, 1768633422559, 1363027763073,
                907489024363, 907489024363, 898671383240, 970587140698, 582429892354,
                570593471433]
              widthNumerator := ![426980463014, 338665935718, 156888336731, 286644659239,
                452249002876, 452249002876, 140739168116, 139746073397, 76077414386,
                295366976765]
            }))
          (.leaf {
            lowerNumerator := ![2259397666791, 1006624833311, 1653278147240, 1488935092332,
              1002571426721, 1002571426721, 833386208401, 865901307245, 526087605952,
              471874231736]
            widthNumerator := ![566550869165, 478782995630, 296761975524, 293371617512,
              578941354360, 578941354360, 250770943105, 192876705952, 165103942829,
              257599280490]
          }))
        (.split 7
          (.split 4
            (.leaf {
              lowerNumerator := ![2296253225372, 1003222681594, 1863750004148, 1363027763073,
                1011832192245, 1011832192245, 933516085063, 970587140698, 639082604079,
                570593471433]
              widthNumerator := ![437343156195, 363616989063, 158464208859, 286644659239,
                450100959934, 450100959934, 151040902748, 139746073397, 85461947404,
                295366976765]
            })
            (.split 7
              (.leaf {
                lowerNumerator := ![2386006163452, 1106556670354, 1964299034011, 1403705572214,
                  1135731231223, 1135731231223, 987269481741, 1026929427100, 710695509622,
                  683290098293]
                widthNumerator := ![310981348588, 262249348526, 159660607166, 152943744576,
                  311190525806, 311190525806, 158283389854, 83403786995, 106353117649,
                  156654377400]
              })
              (.leaf {
                lowerNumerator := ![2444044583885, 1219126464367, 1964299034011, 1457227834620,
                  1252046803548, 1252046803548, 987269481741, 970587140698, 710695509622,
                  602424759608]
                widthNumerator := ![312758967167, 270303445811, 159660607166, 154678549469,
                  304362447087, 304362447087, 158283389854, 81055194624, 106353117649,
                  152698337136]
              })))
          (.split 4
            (.leaf {
              lowerNumerator := ![2409717109169, 1221027901941, 1863750004148, 1488935092332,
                1246024302284, 1246024302284, 933516085063, 865901307245, 639082604079,
                471874231736]
              widthNumerator := ![445189250259, 390101250146, 158464208859, 293371617512,
                433379072801, 433379072801, 151040902748, 192876705952, 85461947404,
                257599280490]
            })
            (.leaf {
              lowerNumerator := ![2474507328979, 1337331740130, 1964299034011, 1488935092332,
                1368132475418, 1368132475418, 987269481741, 865901307245, 710695509622,
                471874231736]
              widthNumerator := ![451461820733, 402042586101, 159660607166, 293371617512,
                428650711624, 428650711624, 158283389854, 192876705952, 106353117649,
                257599280490]
            }))))
      (.split 4
        (.leaf {
          lowerNumerator := ![2306211520223, 1224833615636, 1653278147240, 1604939952548,
            1240643370860, 1240643370860, 833386208401, 732827531891, 526087605952,
            526087605952]
          widthNumerator := ![865079447162, 776653425973, 296761975524, 580746471119,
            821470998945, 821470998945, 250770943105, 523481334141, 165103942829,
            290961021319]
        })
        (.split 7
          (.leaf {
            lowerNumerator := ![2516791219770, 1461815045850, 1843397393523, 1653278147240,
              1496809710019, 1496809710019, 892189527824, 833386208401, 639082604079,
              526087605952]
            widthNumerator := ![593995925029, 539671995759, 299854616692, 296761975524,
              549451178802, 549451178802, 288749083435, 250770943105, 177966023192,
              165103942829]
          })
          (.leaf {
            lowerNumerator := ![2679422771494, 1711790607255, 1843397393523, 1843397393523,
              1752976049178, 1752976049178, 892189527824, 892189527824, 639082604079,
              639082604079]
            widthNumerator := ![601943490612, 557133898144, 299854616692, 299854616692,
              544016533464, 544016533464, 288749083435, 288749083435, 177966023192,
              177966023192]
          }))))

/-- Exact dyadic norm witnesses for antisymmetric face concavity. -/
@[reducible]
def faceHessianCertificateTree : LocalCertificateTree 7 10 :=
  .split 4
    (.split 6
      (.split 4
        (.split 6
          (.leaf {
            lowerNumerator := ![3153143939378, 2230914866415, 2091855756016, 2091855756016,
              2270623740128, 2270623740128, 1095335910599, 1095335910599, 800701269319,
              800701269319]
            widthNumerator := ![15808400617, 28190417699, 7538260387, 7538260387,
              15860091112, 15860091112, 8356591994, 8356591994, 13501509918, 13501509918]
          })
          (.leaf {
            lowerNumerator := ![3152675888587, 2231700435641, 2091855756016, 2091151354932,
              2272190813473, 2269190861484, 1095335910599, 1095336115712, 800701269319,
              800699214406]
            widthNumerator := ![15810053471, 28182334399, 7538260387, 7539979882,
              15852621954, 15845793496, 8356591994, 8356167032, 13501509918, 13505548895]
          }))
        (.split 6
          (.leaf {
            lowerNumerator := ![3152675888587, 2231700435641, 2091151354932, 2091855756016,
              2269190861484, 2272190813473, 1095336115712, 1095335910599, 800699214406,
              800701269319]
            widthNumerator := ![15810053471, 28182334399, 7539979882, 7538260387,
              15845793496, 15852621954, 8356167032, 8356591994, 13505548895, 13501509918]
          })
          (.leaf {
            lowerNumerator := ![3152209474579, 2232487026546, 2091151354932, 2091151354932,
              2270758467192, 2270758467192, 1095336115712, 1095336115712, 800699214406,
              800699214406]
            widthNumerator := ![15811694543, 28174243191, 7539979882, 7539979882,
              15838331624, 15838331624, 8356167032, 8356167032, 13505548895, 13505548895]
          })))
      (.split 4
        (.split 6
          (.leaf {
            lowerNumerator := ![3152205358166, 2232482804046, 2091855756016, 2090445624435,
              2273754555420, 2267757588326, 1095335910599, 1095336365960, 800701269319,
              800697224484]
            widthNumerator := ![15811650220, 28174179192, 7538260387, 7541642226,
              15845089314, 15831484143, 8356591994, 8355651952, 13501509918, 13509458354]
          })
          (.leaf {
            lowerNumerator := ![3151732361353, 2233261979643, 2091855756016, 2089738574335,
              2275314967318, 2266323931308, 1095335910599, 1095336661144, 800701269319,
              800695299405]
            widthNumerator := ![15813191076, 28165952428, 7538260387, 7543247611,
              15837493640, 15817163284, 8356591994, 8355047150, 13501509918, 13513238592]
          }))
        (.split 6
          (.leaf {
            lowerNumerator := ![3151740578715, 2233270415268, 2091151354932, 2090445624435,
              2272322742783, 2269325724449, 1095336115712, 1095336365960, 800699214406,
              800697224484]
            widthNumerator := ![15813279517, 28166080101, 7539979882, 7541642226,
              15830806262, 15824029566, 8356167032, 8355651952, 13505548895, 13509458354]
          })
          (.leaf {
            lowerNumerator := ![3151269214232, 2234050609817, 2091151354932, 2089738574335,
              2273883689592, 2267892595900, 1095336115712, 1095336661144, 800699214406,
              800695299405]
            widthNumerator := ![15814808606, 28157845479, 7539979882, 7543247611,
              15823217860, 15809716016, 8356167032, 8355047150, 13505548895, 13513238592]
          }))))
    (.split 6
      (.split 4
        (.split 6
          (.leaf {
            lowerNumerator := ![3152205358166, 2232482804046, 2090445624435, 2091855756016,
              2267757588326, 2273754555420, 1095336365960, 1095335910599, 800697224484,
              800701269319]
            widthNumerator := ![15811650220, 28174179192, 7541642226, 7538260387,
              15831484143, 15845089314, 8355651952, 8356591994, 13509458354, 13501509918]
          })
          (.leaf {
            lowerNumerator := ![3151740578715, 2233270415268, 2090445624435, 2091151354932,
              2269325724449, 2272322742783, 1095336365960, 1095336115712, 800697224484,
              800699214406]
            widthNumerator := ![15813279517, 28166080101, 7541642226, 7539979882,
              15824029566, 15830806262, 8355651952, 8356167032, 13509458354, 13505548895]
          }))
        (.split 6
          (.leaf {
            lowerNumerator := ![3151732361353, 2233261979643, 2089738574335, 2091855756016,
              2266323931308, 2275314967318, 1095336661144, 1095335910599, 800695299405,
              800701269319]
            widthNumerator := ![15813191076, 28165952428, 7543247611, 7538260387,
              15817163284, 15837493640, 8355047150, 8356591994, 13513238592, 13501509918]
          })
          (.leaf {
            lowerNumerator := ![3151269214232, 2234050609817, 2089738574335, 2091151354932,
              2267892595900, 2273883689592, 1095336661144, 1095336115712, 800695299405,
              800699214406]
            widthNumerator := ![15814808606, 28157845479, 7543247611, 7539979882,
              15809716016, 15823217860, 8355047150, 8356167032, 13513238592, 13505548895]
          })))
      (.split 4
        (.split 6
          (.leaf {
            lowerNumerator := ![3151273315188, 2234054822948, 2090445624435, 2090445624435,
              2270890531734, 2270890531734, 1095336365960, 1095336365960, 800697224484,
              800697224484]
            widthNumerator := ![15814852724, 28157909154, 7541642226, 7541642226,
              15816511494, 15816511494, 8355651952, 8355651952, 13509458354, 13509458354]
          })
          (.leaf {
            lowerNumerator := ![3150803580822, 2234836035095, 2090445624435, 2089738574335,
              2272452011505, 2269457932936, 1095336365960, 1095336661144, 800697224484,
              800695299405]
            widthNumerator := ![15816370053, 28149666700, 7541642226, 7543247611,
              15808930375, 15802205244, 8355651952, 8355047150, 13509458354, 13513238592]
          }))
        (.split 6
          (.leaf {
            lowerNumerator := ![3150803580822, 2234836035095, 2089738574335, 2090445624435,
              2269457932936, 2272452011505, 1095336661144, 1095336365960, 800695299405,
              800697224484]
            widthNumerator := ![15816370053, 28149666700, 7543247611, 7541642226,
              15802205244, 15808930375, 8355047150, 8355651952, 13513238592, 13509458354]
          })
          (.leaf {
            lowerNumerator := ![3150335474359, 2235618263486, 2089738574335, 2089738574335,
              2271019943727, 2271019943727, 1095336661144, 1095336661144, 800695299405,
              800695299405]
            widthNumerator := ![15817875627, 28141416436, 7543247611, 7543247611,
              15794631417, 15794631417, 8355047150, 8355047150, 13513238592, 13513238592]
          }))))

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 5000000 in
private theorem determinant_leaf_40604060 :
    exactPositiveEnclosureCheck faceNegativeHessianDeterminant
      (exactExtendedBox

          (exactSplitLower
            (exactSplitLower
              (exactSplitLower
                (exactSplitLower exactFaceRootBox 4) 6) 4) 6)
        {
          lowerNumerator := ![3153143939378, 2230914866415, 2091855756016, 2091855756016,
            2270623740128, 2270623740128, 1095335910599,
            1095335910599, 800701269319, 800701269319]
          widthNumerator := ![15808400617, 28190417699, 7538260387, 7538260387, 15860091112,
            15860091112, 8356591994, 8356591994, 13501509918, 13501509918]
        }) = true := by
  with_unfolding_all rfl

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 5000000 in
private theorem determinant_leaf_40604061 :
    exactPositiveEnclosureCheck faceNegativeHessianDeterminant
      (exactExtendedBox

          (exactSplitUpper
            (exactSplitLower
              (exactSplitLower
                (exactSplitLower exactFaceRootBox 4) 6) 4) 6)
        {
          lowerNumerator := ![3152675888587, 2231700435641, 2091855756016, 2091151354932,
            2272190813473, 2269190861484, 1095335910599,
            1095336115712, 800701269319, 800699214406]
          widthNumerator := ![15810053471, 28182334399, 7538260387, 7539979882, 15852621954,
            15845793496, 8356591994, 8356167032, 13501509918, 13505548895]
        }) = true := by
  with_unfolding_all rfl

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 5000000 in
private theorem determinant_leaf_40604160 :
    exactPositiveEnclosureCheck faceNegativeHessianDeterminant
      (exactExtendedBox

          (exactSplitLower
            (exactSplitUpper
              (exactSplitLower
                (exactSplitLower exactFaceRootBox 4) 6) 4) 6)
        {
          lowerNumerator := ![3152675888587, 2231700435641, 2091151354932, 2091855756016,
            2269190861484, 2272190813473, 1095336115712,
            1095335910599, 800699214406, 800701269319]
          widthNumerator := ![15810053471, 28182334399, 7539979882, 7538260387, 15845793496,
            15852621954, 8356167032, 8356591994, 13505548895, 13501509918]
        }) = true := by
  with_unfolding_all rfl

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 5000000 in
private theorem determinant_leaf_40604161 :
    exactPositiveEnclosureCheck faceNegativeHessianDeterminant
      (exactExtendedBox

          (exactSplitUpper
            (exactSplitUpper
              (exactSplitLower
                (exactSplitLower exactFaceRootBox 4) 6) 4) 6)
        {
          lowerNumerator := ![3152209474579, 2232487026546, 2091151354932, 2091151354932,
            2270758467192, 2270758467192, 1095336115712,
            1095336115712, 800699214406, 800699214406]
          widthNumerator := ![15811694543, 28174243191, 7539979882, 7539979882, 15838331624,
            15838331624, 8356167032, 8356167032, 13505548895, 13505548895]
        }) = true := by
  with_unfolding_all rfl

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 5000000 in
private theorem determinant_leaf_40614060 :
    exactPositiveEnclosureCheck faceNegativeHessianDeterminant
      (exactExtendedBox

          (exactSplitLower
            (exactSplitLower
              (exactSplitUpper
                (exactSplitLower exactFaceRootBox 4) 6) 4) 6)
        {
          lowerNumerator := ![3152205358166, 2232482804046, 2091855756016, 2090445624435,
            2273754555420, 2267757588326, 1095335910599,
            1095336365960, 800701269319, 800697224484]
          widthNumerator := ![15811650220, 28174179192, 7538260387, 7541642226, 15845089314,
            15831484143, 8356591994, 8355651952, 13501509918, 13509458354]
        }) = true := by
  with_unfolding_all rfl

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 5000000 in
private theorem determinant_leaf_40614061 :
    exactPositiveEnclosureCheck faceNegativeHessianDeterminant
      (exactExtendedBox

          (exactSplitUpper
            (exactSplitLower
              (exactSplitUpper
                (exactSplitLower exactFaceRootBox 4) 6) 4) 6)
        {
          lowerNumerator := ![3151732361353, 2233261979643, 2091855756016, 2089738574335,
            2275314967318, 2266323931308, 1095335910599,
            1095336661144, 800701269319, 800695299405]
          widthNumerator := ![15813191076, 28165952428, 7538260387, 7543247611, 15837493640,
            15817163284, 8356591994, 8355047150, 13501509918, 13513238592]
        }) = true := by
  with_unfolding_all rfl

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 5000000 in
private theorem determinant_leaf_40614160 :
    exactPositiveEnclosureCheck faceNegativeHessianDeterminant
      (exactExtendedBox

          (exactSplitLower
            (exactSplitUpper
              (exactSplitUpper
                (exactSplitLower exactFaceRootBox 4) 6) 4) 6)
        {
          lowerNumerator := ![3151740578715, 2233270415268, 2091151354932, 2090445624435,
            2272322742783, 2269325724449, 1095336115712,
            1095336365960, 800699214406, 800697224484]
          widthNumerator := ![15813279517, 28166080101, 7539979882, 7541642226, 15830806262,
            15824029566, 8356167032, 8355651952, 13505548895, 13509458354]
        }) = true := by
  with_unfolding_all rfl

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 5000000 in
private theorem determinant_leaf_40614161 :
    exactPositiveEnclosureCheck faceNegativeHessianDeterminant
      (exactExtendedBox

          (exactSplitUpper
            (exactSplitUpper
              (exactSplitUpper
                (exactSplitLower exactFaceRootBox 4) 6) 4) 6)
        {
          lowerNumerator := ![3151269214232, 2234050609817, 2091151354932, 2089738574335,
            2273883689592, 2267892595900, 1095336115712,
            1095336661144, 800699214406, 800695299405]
          widthNumerator := ![15814808606, 28157845479, 7539979882, 7543247611, 15823217860,
            15809716016, 8356167032, 8355047150, 13505548895, 13513238592]
        }) = true := by
  with_unfolding_all rfl

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 5000000 in
private theorem determinant_leaf_41604060 :
    exactPositiveEnclosureCheck faceNegativeHessianDeterminant
      (exactExtendedBox

          (exactSplitLower
            (exactSplitLower
              (exactSplitLower
                (exactSplitUpper exactFaceRootBox 4) 6) 4) 6)
        {
          lowerNumerator := ![3152205358166, 2232482804046, 2090445624435, 2091855756016,
            2267757588326, 2273754555420, 1095336365960,
            1095335910599, 800697224484, 800701269319]
          widthNumerator := ![15811650220, 28174179192, 7541642226, 7538260387, 15831484143,
            15845089314, 8355651952, 8356591994, 13509458354, 13501509918]
        }) = true := by
  with_unfolding_all rfl

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 5000000 in
private theorem determinant_leaf_41604061 :
    exactPositiveEnclosureCheck faceNegativeHessianDeterminant
      (exactExtendedBox

          (exactSplitUpper
            (exactSplitLower
              (exactSplitLower
                (exactSplitUpper exactFaceRootBox 4) 6) 4) 6)
        {
          lowerNumerator := ![3151740578715, 2233270415268, 2090445624435, 2091151354932,
            2269325724449, 2272322742783, 1095336365960,
            1095336115712, 800697224484, 800699214406]
          widthNumerator := ![15813279517, 28166080101, 7541642226, 7539979882, 15824029566,
            15830806262, 8355651952, 8356167032, 13509458354, 13505548895]
        }) = true := by
  with_unfolding_all rfl

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 5000000 in
private theorem determinant_leaf_41604160 :
    exactPositiveEnclosureCheck faceNegativeHessianDeterminant
      (exactExtendedBox

          (exactSplitLower
            (exactSplitUpper
              (exactSplitLower
                (exactSplitUpper exactFaceRootBox 4) 6) 4) 6)
        {
          lowerNumerator := ![3151732361353, 2233261979643, 2089738574335, 2091855756016,
            2266323931308, 2275314967318, 1095336661144,
            1095335910599, 800695299405, 800701269319]
          widthNumerator := ![15813191076, 28165952428, 7543247611, 7538260387, 15817163284,
            15837493640, 8355047150, 8356591994, 13513238592, 13501509918]
        }) = true := by
  with_unfolding_all rfl

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 5000000 in
private theorem determinant_leaf_41604161 :
    exactPositiveEnclosureCheck faceNegativeHessianDeterminant
      (exactExtendedBox

          (exactSplitUpper
            (exactSplitUpper
              (exactSplitLower
                (exactSplitUpper exactFaceRootBox 4) 6) 4) 6)
        {
          lowerNumerator := ![3151269214232, 2234050609817, 2089738574335, 2091151354932,
            2267892595900, 2273883689592, 1095336661144,
            1095336115712, 800695299405, 800699214406]
          widthNumerator := ![15814808606, 28157845479, 7543247611, 7539979882, 15809716016,
            15823217860, 8355047150, 8356167032, 13513238592, 13505548895]
        }) = true := by
  with_unfolding_all rfl

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 5000000 in
private theorem determinant_leaf_41614060 :
    exactPositiveEnclosureCheck faceNegativeHessianDeterminant
      (exactExtendedBox

          (exactSplitLower
            (exactSplitLower
              (exactSplitUpper
                (exactSplitUpper exactFaceRootBox 4) 6) 4) 6)
        {
          lowerNumerator := ![3151273315188, 2234054822948, 2090445624435, 2090445624435,
            2270890531734, 2270890531734, 1095336365960,
            1095336365960, 800697224484, 800697224484]
          widthNumerator := ![15814852724, 28157909154, 7541642226, 7541642226, 15816511494,
            15816511494, 8355651952, 8355651952, 13509458354, 13509458354]
        }) = true := by
  with_unfolding_all rfl

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 5000000 in
private theorem determinant_leaf_41614061 :
    exactPositiveEnclosureCheck faceNegativeHessianDeterminant
      (exactExtendedBox

          (exactSplitUpper
            (exactSplitLower
              (exactSplitUpper
                (exactSplitUpper exactFaceRootBox 4) 6) 4) 6)
        {
          lowerNumerator := ![3150803580822, 2234836035095, 2090445624435, 2089738574335,
            2272452011505, 2269457932936, 1095336365960,
            1095336661144, 800697224484, 800695299405]
          widthNumerator := ![15816370053, 28149666700, 7541642226, 7543247611, 15808930375,
            15802205244, 8355651952, 8355047150, 13509458354, 13513238592]
        }) = true := by
  with_unfolding_all rfl

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 5000000 in
private theorem determinant_leaf_41614160 :
    exactPositiveEnclosureCheck faceNegativeHessianDeterminant
      (exactExtendedBox

          (exactSplitLower
            (exactSplitUpper
              (exactSplitUpper
                (exactSplitUpper exactFaceRootBox 4) 6) 4) 6)
        {
          lowerNumerator := ![3150803580822, 2234836035095, 2089738574335, 2090445624435,
            2269457932936, 2272452011505, 1095336661144,
            1095336365960, 800695299405, 800697224484]
          widthNumerator := ![15816370053, 28149666700, 7543247611, 7541642226, 15802205244,
            15808930375, 8355047150, 8355651952, 13513238592, 13509458354]
        }) = true := by
  with_unfolding_all rfl

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 5000000 in
private theorem determinant_leaf_41614161 :
    exactPositiveEnclosureCheck faceNegativeHessianDeterminant
      (exactExtendedBox

          (exactSplitUpper
            (exactSplitUpper
              (exactSplitUpper
                (exactSplitUpper exactFaceRootBox 4) 6) 4) 6)
        {
          lowerNumerator := ![3150335474359, 2235618263486, 2089738574335, 2089738574335,
            2271019943727, 2271019943727, 1095336661144,
            1095336661144, 800695299405, 800695299405]
          widthNumerator := ![15817875627, 28141416436, 7543247611, 7543247611, 15794631417,
            15794631417, 8355047150, 8355047150, 13513238592, 13513238592]
        }) = true := by
  with_unfolding_all rfl

set_option maxHeartbeats 1000000 in
private theorem face_hessian_determinant_positive_tree_exact :
    exactPositiveTreeCertifies faceNegativeHessianDeterminant
      faceHessianCertificateTree exactFaceRootBox = true := by
  simp only [exactPositiveTreeCertifies, Bool.and_eq_true]
  exact ⟨
    ⟨
      ⟨⟨determinant_leaf_40604060, determinant_leaf_40604061⟩,
        ⟨determinant_leaf_40604160, determinant_leaf_40604161⟩⟩,
      ⟨⟨determinant_leaf_40614060, determinant_leaf_40614061⟩,
        ⟨determinant_leaf_40614160, determinant_leaf_40614161⟩⟩
    ⟩,
    ⟨
      ⟨⟨determinant_leaf_41604060, determinant_leaf_41604061⟩,
        ⟨determinant_leaf_41604160, determinant_leaf_41604161⟩⟩,
      ⟨⟨determinant_leaf_41614060, determinant_leaf_41614061⟩,
        ⟨determinant_leaf_41614160, determinant_leaf_41614161⟩⟩
    ⟩
  ⟩

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 5000000 in
/-- The transverse interval tree passes its exact kernel checker. -/
theorem transverse_certificate_tree_exact :
    exactLocalTreeCertifies transverseVectors transverseDerivativeExpression
      transverseCertificateTree exactTransverseRootBox = true := by
  with_unfolding_all rfl

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 5000000 in
/-- The face interval tree proves positivity of the first negative-Hessian pivot. -/
theorem face_hessian_pivot_tree_exact :
    exactLocalTreeCertifies faceVectors faceNegativeHessian00
      faceHessianCertificateTree exactFaceRootBox = true := by
  with_unfolding_all rfl

/-- The face interval tree proves positivity of the negative-Hessian determinant. -/
theorem face_hessian_determinant_tree_exact :
    exactLocalTreeCertifies faceVectors faceNegativeHessianDeterminant
      faceHessianCertificateTree exactFaceRootBox = true :=
  exact_local_tree_of_positive_tree faceVectors faceNegativeHessian00
    faceNegativeHessianDeterminant faceHessianCertificateTree exactFaceRootBox
    face_hessian_pivot_tree_exact face_hessian_determinant_positive_tree_exact

end WeightedMixedEqualityLocal

end Bescovitch
