/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import Bescovitch.SixPoint.WeightedMixedCertificateData.Basic

/-!
# Mixed weighted certificate data for chart `(0, 1, 1, -1)`

This generated tree covers cap choices `0, 1` and stereographic side signs `1, -1`.
Every numerical leaf stores exact integer numerators with common denominator `4096`.
-/

@[expose] public section

namespace Bescovitch

/-- Assemble one exact q12 leaf for chart `(0, 1, 1, -1)`. -/
def weightedMixedLeafCap0Cap1SidePosSideNeg
    (r0 r1 r2 r3 r4 r5 : ℕ) (s0 s1 s2 s3 : ℤ) (e0 e1 e2 e3 : ℕ) :
    WeightedMixedLeaf where
  rhoNumerator
    | 0 => r0
    | 1 => r1
    | 2 => r2
    | 3 => r3
    | 4 => r4
    | 5 => r5
  supportSlopeNumerator
    | 0 => s0
    | 1 => s1
    | 2 => s2
    | 3 => s3
  slackNumerator
    | 0 => e0
    | 1 => e1
    | 2 => e2
    | 3 => e3

set_option maxRecDepth 20000 in
/-- The exact mixed-certificate tree for chart `(0, 1, 1, -1)`. -/
def weightedMixedTreeCap0Cap1SidePosSideNeg : WeightedMixedTree :=
  (.split
    (.split
      (.split
        (.split
          (.split (.split (.certified (weightedMixedLeafCap0Cap1SidePosSideNeg 1775 7354 5218 6406 2859 10888 (-351) (-16396) (-8907) 3651 0 1777 2252 0)) (.certified (weightedMixedLeafCap0Cap1SidePosSideNeg 1775 5893 3866 5842 1823 7457 (-351) 5039 (-8907) (-827) 0 2788 4317 0))) (.split (.certified (weightedMixedLeafCap0Cap1SidePosSideNeg 1775 5893 4530 4487 1211 9881 (-351) (-5039) (-8907) 827 0 13129 9106 0)) (.certified (weightedMixedLeafCap0Cap1SidePosSideNeg 1775 7354 4955 8767 3596 9917 (-351) 16396 (-8907) (-3651) 0 6137 646 0))))
          (.split (.split (.certified (weightedMixedLeafCap0Cap1SidePosSideNeg 1775 7843 5771 6814 2666 11449 (-351) (-14373) (-8907) 4168 0 1611 939 0)) (.certified (weightedMixedLeafCap0Cap1SidePosSideNeg 1775 6494 4493 5773 1198 7871 (-351) 5392 (-8907) (-549) 0 3675 4716 0))) (.split (.certified (weightedMixedLeafCap0Cap1SidePosSideNeg 1775 6494 5157 5053 633 10496 (-351) (-5392) (-8907) 549 0 4236 14571 0)) (.certified (weightedMixedLeafCap0Cap1SidePosSideNeg 1775 7843 5459 8722 3323 10232 (-351) 14373 (-8907) (-4168) 0 1184 5300 0)))))
        (.split
          (.split (.split (.certified (weightedMixedLeafCap0Cap1SidePosSideNeg 2568 7354 5226 3589 4680 8870 1326 (-16396) (-3750) 3651 0 0 1040 0)) (.certified (weightedMixedLeafCap0Cap1SidePosSideNeg 2568 5893 5602 5283 613 4495 1326 5039 (-3750) (-827) 0 0 10263 0))) (.split (.certified (weightedMixedLeafCap0Cap1SidePosSideNeg 2568 5893 3490 3090 2602 8680 1326 (-5039) (-3750) 827 0 0 6883 0)) (.certified (weightedMixedLeafCap0Cap1SidePosSideNeg 2568 7354 6044 7739 2352 7224 1326 16396 (-3750) (-3651) 0 0 2624 0))))
          (.split (.split (.certified (weightedMixedLeafCap0Cap1SidePosSideNeg 2568 7843 5645 4121 4396 9482 1326 (-14373) (-3750) 4168 0 0 0 0)) (.certified (weightedMixedLeafCap0Cap1SidePosSideNeg 2568 6494 6227 4887 795 4828 1326 5392 (-3750) (-549) 0 0 7680 0))) (.split (.certified (weightedMixedLeafCap0Cap1SidePosSideNeg 2568 6494 4091 3695 2048 9305 1326 (-5392) (-3750) 549 0 0 5378 0)) (.certified (weightedMixedLeafCap0Cap1SidePosSideNeg 2568 7843 6628 7474 2405 7436 1326 14373 (-3750) (-4168) 0 0 1718 0))))))
      (.split
        (.split
          (.split
            (.split (.certified (weightedMixedLeafCap0Cap1SidePosSideNeg 3812 7354 6214 8162 5810 11398 2657 (-16396) (-69408) 3651 0 6194 4404 0)) (.split (.split (.certified (weightedMixedLeafCap0Cap1SidePosSideNeg 3258 5893 6075 5722 2048 8908 1956 5039 (-26672) (-827) 0 1524 5504 0)) (.certified (weightedMixedLeafCap0Cap1SidePosSideNeg 3580 5893 6456 5761 781 9172 3431 5039 371101 (-827) 0 29648 7833 0))) (.split (.certified (weightedMixedLeafCap0Cap1SidePosSideNeg 3088 5893 6036 5409 2048 8679 1816 5039 (-28136) (-827) 0 0 5605 0)) (.certified (weightedMixedLeafCap0Cap1SidePosSideNeg 4140 5893 7201 5616 1590 9525 3155 5039 140455 (-827) 0 12387 6451 0)))))
            (.split (.certified (weightedMixedLeafCap0Cap1SidePosSideNeg 3812 5893 4015 5471 3357 9656 2657 (-5039) (-69408) 827 0 10148 0 0)) (.split (.certified (weightedMixedLeafCap0Cap1SidePosSideNeg 3580 7354 7061 8632 2964 11200 2782 16396 (-62225) (-3651) 0 10004 5784 0)) (.split (.certified (weightedMixedLeafCap0Cap1SidePosSideNeg 3088 7354 6567 8311 2632 10731 1816 16396 (-28136) (-3651) 0 0 5706 0)) (.certified (weightedMixedLeafCap0Cap1SidePosSideNeg 4140 7354 7582 8385 2857 11380 3155 16396 140455 (-3651) 0 8723 8528 0))))))
          (.split (.split (.certified (weightedMixedLeafCap0Cap1SidePosSideNeg 3812 7843 6566 8394 5579 11870 2657 (-14373) (-69408) 4168 0 6493 2499 0)) (.certified (weightedMixedLeafCap0Cap1SidePosSideNeg 3812 6494 7414 5913 1754 9835 2657 5392 (-69408) (-549) 0 11044 6138 0))) (.split (.certified (weightedMixedLeafCap0Cap1SidePosSideNeg 3812 6494 4541 5810 2938 10208 2657 (-5392) (-69408) 549 0 10466 0 0)) (.certified (weightedMixedLeafCap0Cap1SidePosSideNeg 3812 7843 7868 8663 3165 11696 2657 14373 (-69408) (-4168) 0 6610 7052 0)))))
        (.split
          (.split (.split (.certified (weightedMixedLeafCap0Cap1SidePosSideNeg 5460 7354 8077 6245 6930 10798 6029 (-16396) (-8320) 3651 0 4522 4211 0)) (.certified (weightedMixedLeafCap0Cap1SidePosSideNeg 5460 5893 8016 5828 2536 7286 6029 5039 (-8320) (-827) 0 7996 5047 0))) (.split (.certified (weightedMixedLeafCap0Cap1SidePosSideNeg 5460 5893 5813 4400 4072 9846 6029 (-5039) (-8320) 827 0 7616 3498 0)) (.certified (weightedMixedLeafCap0Cap1SidePosSideNeg 5460 7354 8937 8741 4695 9773 6029 16396 (-8320) (-3651) 0 8454 6330 0))))
          (.split (.split (.certified (weightedMixedLeafCap0Cap1SidePosSideNeg 5460 7843 8432 6664 6838 11364 6029 (-14373) (-8320) 4168 0 6358 1609 0)) (.certified (weightedMixedLeafCap0Cap1SidePosSideNeg 5460 6494 8638 5736 3107 7692 6029 5392 (-8320) (-549) 0 7885 3728 0))) (.split (.certified (weightedMixedLeafCap0Cap1SidePosSideNeg 5460 6494 6297 4976 3913 10464 6029 (-5392) (-8320) 549 0 9435 2433 0)) (.certified (weightedMixedLeafCap0Cap1SidePosSideNeg 5460 7843 9499 8680 5026 10079 6029 14373 (-8320) (-4168) 0 5902 4997 0)))))))
    (.split
      (.split
        (.split
          (.split (.split (.certified (weightedMixedLeafCap0Cap1SidePosSideNeg 1178 7354 4593 5851 2916 10260 (-80) (-16396) (-8188) 3651 0 194 0 0)) (.certified (weightedMixedLeafCap0Cap1SidePosSideNeg 1178 5893 3796 5248 1970 6924 (-80) 5039 (-8188) (-827) 0 0 2324 0))) (.split (.certified (weightedMixedLeafCap0Cap1SidePosSideNeg 1178 5893 3995 3859 1834 9270 (-80) (-5039) (-8188) 827 0 8154 11870 0)) (.certified (weightedMixedLeafCap0Cap1SidePosSideNeg 1178 7354 4511 8162 3134 9328 (-80) 16396 (-8188) (-3651) 0 1801 7715 0))))
          (.split (.split (.certified (weightedMixedLeafCap0Cap1SidePosSideNeg 1178 7843 5143 6238 2592 10821 (-80) (-14373) (-8188) 4168 0 1980 7752 0)) (.certified (weightedMixedLeafCap0Cap1SidePosSideNeg 1178 6494 4420 5160 1368 7359 (-80) 5392 (-8188) (-549) 0 1845 11878 0))) (.split (.certified (weightedMixedLeafCap0Cap1SidePosSideNeg 1178 6494 4617 4425 1258 9887 (-80) (-5392) (-8188) 549 1283 7296 11910 0)) (.certified (weightedMixedLeafCap0Cap1SidePosSideNeg 1178 7843 5047 8106 2795 9656 (-80) 14373 (-8188) (-4168) 0 1567 6182 0)))))
        (.split
          (.split (.split (.certified (weightedMixedLeafCap0Cap1SidePosSideNeg 2817 7354 5059 3272 5183 8356 1632 (-16396) (-3510) 3651 0 0 1340 0)) (.certified (weightedMixedLeafCap0Cap1SidePosSideNeg 2817 5893 6048 4657 1137 4274 1632 5039 (-3510) (-827) 0 0 7220 0))) (.split (.certified (weightedMixedLeafCap0Cap1SidePosSideNeg 2817 5893 3025 2463 3229 8074 1632 (-5039) (-3510) 827 0 0 7094 0)) (.certified (weightedMixedLeafCap0Cap1SidePosSideNeg 2817 7354 6226 7121 1866 6876 1632 16396 (-3510) (-3651) 0 0 4641 0))))
          (.split (.split (.certified (weightedMixedLeafCap0Cap1SidePosSideNeg 2817 7843 5423 3751 4853 8962 1632 (-14373) (-3510) 4168 0 0 0 0)) (.certified (weightedMixedLeafCap0Cap1SidePosSideNeg 2817 6494 6667 4259 1422 4674 1632 5392 (-3510) (-549) 0 0 5263 0))) (.split (.certified (weightedMixedLeafCap0Cap1SidePosSideNeg 2817 6494 3602 3071 2667 8699 1632 (-5392) (-3510) 549 0 0 5113 0)) (.certified (weightedMixedLeafCap0Cap1SidePosSideNeg 2817 7843 6829 6867 2052 7132 1632 14373 (-3510) (-4168) 0 0 2734 0))))))
      (.split
        (.split
          (.split
            (.split (.certified (weightedMixedLeafCap0Cap1SidePosSideNeg 3573 7354 5699 7734 5838 10801 2288 (-16396) (-156699) 3651 0 6464 6356 0)) (.split (.split (.split (.certified (weightedMixedLeafCap0Cap1SidePosSideNeg 2369 5893 5423 4947 733 8841 1157 5039 (-278519) (-827) 0 0 12770 0)) (.certified (weightedMixedLeafCap0Cap1SidePosSideNeg 3505 5893 6542 5175 984 7990 2290 5039 (-16100) (-827) 0 0 9426 0))) (.certified (weightedMixedLeafCap0Cap1SidePosSideNeg 4325 5893 7489 5414 1965 9560 2929 5039 82331 (-827) 0 9341 6633 0))) (.split (.certified (weightedMixedLeafCap0Cap1SidePosSideNeg 2824 5893 6008 4782 995 8237 1632 5039 (-32793) (-827) 0 0 10040 0)) (.certified (weightedMixedLeafCap0Cap1SidePosSideNeg 4245 5893 7484 5120 2082 9368 2742 5039 55899 (-827) 0 8827 6891 0)))))
            (.split
              (.certified (weightedMixedLeafCap0Cap1SidePosSideNeg 3573 5893 3400 4969 3628 9029 2288 (-5039) (-156699) 827 5385 6128 0 0))
              (.split
                (.split (.certified (weightedMixedLeafCap0Cap1SidePosSideNeg 2942 7354 6405 7997 2318 10463 1712 16396 (-30082) (-3651) 0 0 9159 0)) (.split (.certified (weightedMixedLeafCap0Cap1SidePosSideNeg 3598 7354 6958 7679 2018 11319 2239 16396 23814 (-3651) 0 5112 6181 0)) (.certified (weightedMixedLeafCap0Cap1SidePosSideNeg 4959 7354 8393 8434 3447 11176 3699 16396 (-63830) (-3651) 0 7636 7481 0))))
                (.split (.certified (weightedMixedLeafCap0Cap1SidePosSideNeg 2824 7354 6255 7683 2004 10198 1632 16396 (-32793) (-3651) 0 0 9847 0)) (.split (.certified (weightedMixedLeafCap0Cap1SidePosSideNeg 3470 7354 6775 7365 1709 11047 2077 16396 20873 (-3651) 0 5578 9016 0)) (.split (.split (.certified (weightedMixedLeafCap0Cap1SidePosSideNeg 4924 6773 8003 7380 2649 10331 3476 11472 (-100712) (-2789) 3346 3848 0 0)) (.certified (weightedMixedLeafCap0Cap1SidePosSideNeg 4924 7739 8406 8821 3692 11404 3476 27947 (-100712) (-4291) 2868 3529 7072 0))) (.split (.certified (weightedMixedLeafCap0Cap1SidePosSideNeg 4924 7028 8312 7461 2913 10559 3476 11083 (-100712) (-2891) 3488 3507 0 0)) (.certified (weightedMixedLeafCap0Cap1SidePosSideNeg 4924 7964 8701 8889 3886 11612 3476 24011 (-100712) (-4565) 3011 3295 6637 0)))))))))
          (.split
            (.split
              (.split (.certified (weightedMixedLeafCap0Cap1SidePosSideNeg 3624 7843 6157 8046 5546 11416 2365 (-14373) (-115939) 4168 0 6818 3476 0)) (.split (.certified (weightedMixedLeafCap0Cap1SidePosSideNeg 2824 7843 5531 7317 4809 10929 1632 (-14373) (-32793) 4168 0 0 1048 0)) (.split (.certified (weightedMixedLeafCap0Cap1SidePosSideNeg 3470 7843 5531 8491 5611 11020 2077 (-14373) 20873 4168 0 4360 2851 0)) (.certified (weightedMixedLeafCap0Cap1SidePosSideNeg 4924 7843 7099 8128 6842 11521 3476 (-14373) (-100712) 4168 2782 2346 2105 0)))))
              (.split (.split (.certified (weightedMixedLeafCap0Cap1SidePosSideNeg 2942 6494 6639 5275 1134 8971 1712 5392 (-30082) (-549) 0 0 7794 0)) (.certified (weightedMixedLeafCap0Cap1SidePosSideNeg 4325 6494 8113 5745 2542 10111 2929 5392 82331 (-549) 0 8741 4793 0))) (.split (.certified (weightedMixedLeafCap0Cap1SidePosSideNeg 2824 6494 6629 4967 1304 8762 1632 5392 (-32793) (-549) 0 0 7511 0)) (.certified (weightedMixedLeafCap0Cap1SidePosSideNeg 4245 6494 8105 5463 2622 9926 2742 5392 55899 (-549) 5392 3231 5137 0)))))
            (.split
              (.split
                (.split (.certified (weightedMixedLeafCap0Cap1SidePosSideNeg 2942 6494 4056 5053 2399 9730 1712 (-5392) (-30082) 549 0 0 0 0)) (.split (.certified (weightedMixedLeafCap0Cap1SidePosSideNeg 3598 6494 3631 5869 3361 9303 2239 (-5392) 23814 549 0 7919 0 0)) (.certified (weightedMixedLeafCap0Cap1SidePosSideNeg 4959 6494 4904 5728 4121 10148 3699 (-5392) (-63830) 549 0 8683 0 0))))
                (.split (.certified (weightedMixedLeafCap0Cap1SidePosSideNeg 2824 6494 3742 4770 2558 9416 1632 (-5392) (-32793) 549 0 0 0 0)) (.split (.certified (weightedMixedLeafCap0Cap1SidePosSideNeg 3470 6494 3319 5611 3450 8990 2077 (-5392) 20873 549 0 8403 13035 0)) (.split (.certified (weightedMixedLeafCap0Cap1SidePosSideNeg 4924 6344 4538 5415 4336 9707 3476 (-5311) (-100712) 628 0 8679 0 0)) (.certified (weightedMixedLeafCap0Cap1SidePosSideNeg 4924 6749 5011 5881 4444 10151 3476 (-5468) (-100712) 461 3896 4285 12140 0))))))
              (.split (.split (.certified (weightedMixedLeafCap0Cap1SidePosSideNeg 2942 7843 6995 8113 2479 10885 1712 14373 (-30082) (-4168) 0 0 4584 0)) (.certified (weightedMixedLeafCap0Cap1SidePosSideNeg 4325 7843 8327 8346 3161 11785 2929 14373 82331 (-4168) 0 6694 8062 0))) (.split (.certified (weightedMixedLeafCap0Cap1SidePosSideNeg 2824 7843 6853 7800 2174 10627 1632 14373 (-32793) (-4168) 0 0 5965 0)) (.split (.certified (weightedMixedLeafCap0Cap1SidePosSideNeg 3470 7843 7390 7653 2121 11554 2077 14373 20873 (-4168) 268 4847 5159 0)) (.certified (weightedMixedLeafCap0Cap1SidePosSideNeg 4924 7843 8931 8305 3718 11408 3476 14373 (-100712) (-4168) 2331 2893 7212 0))))))))
        (.split
          (.split
            (.split
              (.split
                (.certified (weightedMixedLeafCap0Cap1SidePosSideNeg 5544 7354 7992 6107 7188 10482 5403 (-16396) (-8841) 3651 0 5994 5939 0))
                (.split (.certified (weightedMixedLeafCap0Cap1SidePosSideNeg 4916 7354 7218 5314 6796 9723 4034 (-16396) (-7108) 3651 0 0 1765 0)) (.split (.certified (weightedMixedLeafCap0Cap1SidePosSideNeg 5962 7354 8172 7163 7776 10998 5200 (-16396) (-16703) 3651 3168 1685 3407 0)) (.split (.split (.certified (weightedMixedLeafCap0Cap1SidePosSideNeg 6628 7739 9688 6896 8858 10920 7374 (-27947) (-9669) 4291 0 5729 5778 0)) (.certified (weightedMixedLeafCap0Cap1SidePosSideNeg 6628 6773 8382 5669 7407 10190 7374 (-11472) (-9669) 2789 3721 1040 0 0))) (.split (.certified (weightedMixedLeafCap0Cap1SidePosSideNeg 6628 7964 9828 7059 8811 11184 7374 (-24011) (-9669) 4565 4269 431 5395 0)) (.certified (weightedMixedLeafCap0Cap1SidePosSideNeg 6628 7028 8544 5867 7351 10473 7374 (-11083) (-9669) 2891 3792 1143 0 0)))))))
              (.certified (weightedMixedLeafCap0Cap1SidePosSideNeg 5581 5893 8334 5268 2711 7152 5246 5039 (-9059) (-827) 0 8335 1825 0)))
            (.split
              (.split (.certified (weightedMixedLeafCap0Cap1SidePosSideNeg 5544 5893 5608 4083 4387 9448 5403 (-5039) (-8841) 827 0 9486 3324 0)) (.split (.certified (weightedMixedLeafCap0Cap1SidePosSideNeg 4916 5893 4806 3323 4146 8794 4034 (-5039) (-7108) 827 0 0 3556 0)) (.certified (weightedMixedLeafCap0Cap1SidePosSideNeg 6335 5893 6185 4506 5143 9618 6220 (-5039) (-12141) 827 3767 4201 2390 0))))
              (.split
                (.split
                  (.certified (weightedMixedLeafCap0Cap1SidePosSideNeg 4827 7354 8307 7980 3830 8905 4171 16396 (-6929) (-3651) 0 0 4199 0))
                  (.split
                    (.split (.split (.certified (weightedMixedLeafCap0Cap1SidePosSideNeg 5923 6773 8991 7974 4061 9925 5543 11472 (-15158) (-2789) 0 3935 0 0)) (.certified (weightedMixedLeafCap0Cap1SidePosSideNeg 5923 7739 9572 9450 5223 11145 5543 27947 (-15158) (-4291) 0 6721 5924 0))) (.split (.certified (weightedMixedLeafCap0Cap1SidePosSideNeg 5923 7028 9289 7990 4285 10116 5543 11083 (-15158) (-2891) 0 4448 0 0)) (.certified (weightedMixedLeafCap0Cap1SidePosSideNeg 5923 7964 9852 9463 5399 11315 5543 24011 (-15158) (-4565) 0 6054 6110 0))))
                    (.split (.split (.certified (weightedMixedLeafCap0Cap1SidePosSideNeg 6534 6773 9544 7982 4957 9176 7942 11472 (-9071) (-2789) 0 4438 0 0)) (.certified (weightedMixedLeafCap0Cap1SidePosSideNeg 6534 7739 10241 9447 6193 10476 7942 27947 (-9071) (-4291) 0 6571 5345 0))) (.split (.certified (weightedMixedLeafCap0Cap1SidePosSideNeg 6534 7028 9831 7947 5154 9339 7942 11083 (-9071) (-2891) 0 4715 0 0)) (.certified (weightedMixedLeafCap0Cap1SidePosSideNeg 6534 7964 10509 9418 6352 10619 7942 24011 (-9071) (-4565) 0 5911 5048 0))))))
                (.split
                  (.certified (weightedMixedLeafCap0Cap1SidePosSideNeg 4916 7354 8385 7699 3721 8778 4034 16396 (-7108) (-3651) 0 0 7072 576))
                  (.split
                    (.split
                      (.split (.certified (weightedMixedLeafCap0Cap1SidePosSideNeg 5962 6773 9041 7701 3971 9790 5200 11472 (-16703) (-2789) 4574 2197 0 0)) (.split (.certified (weightedMixedLeafCap0Cap1SidePosSideNeg 5962 7801 9053 7829 3589 11315 5200 (-55899) (-16703) (-2742) 0 6510 5280 0)) (.certified (weightedMixedLeafCap0Cap1SidePosSideNeg 5962 7412 9685 10058 6287 10377 5200 12141 (-16703) (-6220) 3938 1592 5771 0))))
                      (.split (.split (.certified (weightedMixedLeafCap0Cap1SidePosSideNeg 5962 7420 9235 6646 3556 10699 5200 30082 (-16703) (-1712) 4023 2667 0 0)) (.certified (weightedMixedLeafCap0Cap1SidePosSideNeg 5962 6456 9122 8549 5037 9120 5200 6929 (-16703) (-4171) 4055 1806 0 0))) (.split (.certified (weightedMixedLeafCap0Cap1SidePosSideNeg 5962 8069 9363 7956 3875 11558 5200 (-82331) (-16703) (-2929) 3458 2987 4820 0)) (.certified (weightedMixedLeafCap0Cap1SidePosSideNeg 5962 7592 9934 9992 6391 10485 5200 11263 (-16703) (-6658) 3969 1551 5249 0)))))
                    (.split
                      (.split
                        (.certified (weightedMixedLeafCap0Cap1SidePosSideNeg 6628 6773 9662 7737 4928 9105 7374 11472 (-9669) (-2789) 5329 992 0 0))
                        (.split
                          (.split (.certified (weightedMixedLeafCap0Cap1SidePosSideNeg 6603 7801 9909 8032 4632 10895 7503 (-55899) (-9506) (-2742) 0 6354 5392 0)) (.split (.certified (weightedMixedLeafCap0Cap1SidePosSideNeg 6307 7801 9560 7697 4239 10495 6570 (-55899) (-8769) (-2742) 0 0 5091 0)) (.certified (weightedMixedLeafCap0Cap1SidePosSideNeg 7003 7801 10293 8120 4966 11166 7946 (-55899) (-10996) (-2742) 0 5850 5010 0))))
                          (.split
                            (.certified (weightedMixedLeafCap0Cap1SidePosSideNeg 6603 7412 10281 10028 7326 9676 7503 12141 (-9506) (-6220) 0 5416 5437 0))
                            (.split (.certified (weightedMixedLeafCap0Cap1SidePosSideNeg 6307 7412 10004 9655 6935 9284 6570 12141 (-8769) (-6220) 0 0 4468 0)) (.split (.certified (weightedMixedLeafCap0Cap1SidePosSideNeg 6867 7412 10561 10217 7433 10186 7280 12141 (-12357) (-6220) 4098 893 5177 0)) (.split (.split (.certified (weightedMixedLeafCap0Cap1SidePosSideNeg 7122 7064 10470 9835 7497 9461 8664 10828 (-9939) (-5585) 3972 1107 0 0)) (.certified (weightedMixedLeafCap0Cap1SidePosSideNeg 7122 7679 10995 10529 8214 10180 8664 14177 (-9939) (-6661) 4486 486 5017 0))) (.split (.certified (weightedMixedLeafCap0Cap1SidePosSideNeg 7122 7155 10584 9781 7538 9499 8664 10457 (-9939) (-5748) 4503 646 0 0)) (.certified (weightedMixedLeafCap0Cap1SidePosSideNeg 7122 7763 11103 10478 8251 10215 8664 13518 (-9939) (-6885) 4524 443 4900 0)))))))))
                      (.split
                        (.split (.certified (weightedMixedLeafCap0Cap1SidePosSideNeg 6628 7420 9979 6647 4356 10113 7374 30082 (-9669) (-1712) 4897 1629 0 0)) (.certified (weightedMixedLeafCap0Cap1SidePosSideNeg 6628 6456 9613 8481 5998 8329 7374 6929 (-9669) (-4171) 4673 1123 0 0)))
                        (.split
                          (.split
                            (.certified (weightedMixedLeafCap0Cap1SidePosSideNeg 6603 8069 10213 8113 4900 11117 7503 (-82331) (-9506) (-2929) 0 6284 5002 0))
                            (.split (.certified (weightedMixedLeafCap0Cap1SidePosSideNeg 6307 8069 9866 7770 4511 10716 6570 (-82331) (-8769) (-2929) 0 0 4695 0)) (.split (.certified (weightedMixedLeafCap0Cap1SidePosSideNeg 6867 8069 10416 8199 5013 11511 7280 (-82331) (-12357) (-2929) 3719 2008 4451 0)) (.split (.certified (weightedMixedLeafCap0Cap1SidePosSideNeg 7122 8002 10683 8199 5381 11215 8664 (-74022) (-9939) (-2879) 4091 1542 4665 0)) (.split (.split (.certified (weightedMixedLeafCap0Cap1SidePosSideNeg 7122 7893 10422 7208 4764 11228 8664 (-32630) (-9939) (-2047) 0 5193 3334 0)) (.certified (weightedMixedLeafCap0Cap1SidePosSideNeg 7122 7907 10930 8493 5983 10798 8664 37243 (-9939) (-3435) 0 5147 5788 0))) (.certified (weightedMixedLeafCap0Cap1SidePosSideNeg 7122 8180 10857 8327 5560 11387 8664 (-50711) (-9939) (-3230) 0 5512 8019 0)))))))
                          (.split
                            (.certified (weightedMixedLeafCap0Cap1SidePosSideNeg 6603 7592 10510 9924 7407 9753 7503 11263 (-9506) (-6658) 0 5406 5109 0))
                            (.split (.certified (weightedMixedLeafCap0Cap1SidePosSideNeg 6307 7592 10239 9547 7021 9365 6570 11263 (-8769) (-6658) 0 0 4055 0)) (.split (.certified (weightedMixedLeafCap0Cap1SidePosSideNeg 6867 7592 10795 10133 7528 10276 7280 11263 (-12357) (-6658) 4134 820 4868 0)) (.split (.split (.certified (weightedMixedLeafCap0Cap1SidePosSideNeg 7122 7249 10699 9729 7581 9539 8664 10132 (-9939) (-5932) 4566 594 0 0)) (.certified (weightedMixedLeafCap0Cap1SidePosSideNeg 7122 7794 11165 10366 8226 10188 8664 12946 (-9939) (-7135) 4535 451 5104 0))) (.split (.certified (weightedMixedLeafCap0Cap1SidePosSideNeg 7122 7345 10814 9679 7628 9582 8664 9845 (-9939) (-6141) 4583 566 5920 0)) (.certified (weightedMixedLeafCap0Cap1SidePosSideNeg 7122 7708 11125 10112 8062 10019 8664 12447 (-9939) (-7416) 4338 460 6019 0)))))))))))))))
          (.split
            (.split
              (.split
                (.split
                  (.certified (weightedMixedLeafCap0Cap1SidePosSideNeg 4827 7843 7599 5801 6431 10508 4171 (-14373) (-6929) 4168 0 0 113 0))
                  (.split (.split (.certified (weightedMixedLeafCap0Cap1SidePosSideNeg 5923 7719 8473 7503 7526 11611 5543 (-14781) (-15158) 4013 0 5111 1380 0)) (.split (.certified (weightedMixedLeafCap0Cap1SidePosSideNeg 5923 7764 8333 7391 7122 11692 5543 (-19443) (-15158) 5334 0 5167 7862 0)) (.certified (weightedMixedLeafCap0Cap1SidePosSideNeg 5923 7552 8011 7085 6742 11501 5543 (-10528) (-15158) 3206 0 5891 0 0)))) (.split (.certified (weightedMixedLeafCap0Cap1SidePosSideNeg 6534 7719 9353 6693 7863 11258 7942 (-14781) (-9071) 4013 0 5055 2334 0)) (.split (.certified (weightedMixedLeafCap0Cap1SidePosSideNeg 6534 7764 9239 6648 7494 11389 7942 (-19443) (-9071) 5334 0 5158 7942 0)) (.certified (weightedMixedLeafCap0Cap1SidePosSideNeg 6534 7552 8930 6381 7109 11235 7942 (-10528) (-9071) 3206 0 5770 0 0))))))
                (.split
                  (.certified (weightedMixedLeafCap0Cap1SidePosSideNeg 4916 7843 7531 5692 6608 10287 4034 (-14373) (-7108) 4168 0 0 0 0))
                  (.split
                    (.split (.split (.certified (weightedMixedLeafCap0Cap1SidePosSideNeg 5962 7992 8763 7765 8071 11632 5200 (-21354) (-16703) 4904 4392 668 4911 0)) (.certified (weightedMixedLeafCap0Cap1SidePosSideNeg 5962 7288 7731 6766 6936 10991 5200 (-10776) (-16703) 3025 4120 1505 0 0))) (.split (.certified (weightedMixedLeafCap0Cap1SidePosSideNeg 5962 7764 8222 7262 7238 11459 5200 (-19443) (-16703) 5334 4903 673 8040 0)) (.split (.certified (weightedMixedLeafCap0Cap1SidePosSideNeg 5962 6905 6724 7622 7348 10626 5200 (-6667) (-16703) 4607 4647 2223 7564 0)) (.certified (weightedMixedLeafCap0Cap1SidePosSideNeg 5962 8010 9001 6216 6115 11597 5200 (-26672) (-16703) 1956 4028 1595 9735 0)))))
                    (.split (.split (.certified (weightedMixedLeafCap0Cap1SidePosSideNeg 6628 7992 9709 6982 8470 11295 7374 (-21354) (-9669) 4904 4293 336 5161 0)) (.certified (weightedMixedLeafCap0Cap1SidePosSideNeg 6628 7288 8714 6074 7307 10757 7374 (-10776) (-9669) 3025 4775 682 0 0))) (.split (.certified (weightedMixedLeafCap0Cap1SidePosSideNeg 6628 7764 9208 6571 7661 11205 7374 (-19443) (-9669) 5334 4655 404 7906 0)) (.split (.certified (weightedMixedLeafCap0Cap1SidePosSideNeg 6628 6905 7770 6955 7824 10551 7374 (-6667) (-9669) 4607 0 6277 7810 0)) (.certified (weightedMixedLeafCap0Cap1SidePosSideNeg 6628 8010 9913 5630 6487 11204 7374 (-26672) (-9669) 1956 4772 832 9714 0))))))))
              (.split (.certified (weightedMixedLeafCap0Cap1SidePosSideNeg 5544 6494 8877 5341 3259 7615 5403 5392 (-8841) (-549) 0 8507 2930 0)) (.split (.certified (weightedMixedLeafCap0Cap1SidePosSideNeg 4916 6494 8440 4686 2762 6845 4034 5392 (-7108) (-549) 0 0 3755 0)) (.split (.certified (weightedMixedLeafCap0Cap1SidePosSideNeg 5962 6494 9443 5600 3778 8765 5200 5392 (-16703) (-549) 0 7384 2463 0)) (.certified (weightedMixedLeafCap0Cap1SidePosSideNeg 6628 6494 9820 5480 4295 7874 7374 5392 (-9669) (-549) 6117 850 1820 0))))))
            (.split
              (.split
                (.split (.certified (weightedMixedLeafCap0Cap1SidePosSideNeg 4827 6494 5422 4137 3607 9689 4171 (-5392) (-6929) 549 0 0 2862 0)) (.split (.certified (weightedMixedLeafCap0Cap1SidePosSideNeg 5923 6494 6190 5395 4623 10460 5543 (-5392) (-15158) 549 0 8400 504 0)) (.certified (weightedMixedLeafCap0Cap1SidePosSideNeg 6534 6494 7177 5000 4908 10427 7942 (-5392) (-9071) 549 0 7943 1885 0))))
                (.split
                  (.certified (weightedMixedLeafCap0Cap1SidePosSideNeg 4916 6494 5264 3899 3830 9415 4034 (-5392) (-7108) 549 0 0 2524 0))
                  (.split
                    (.split (.certified (weightedMixedLeafCap0Cap1SidePosSideNeg 5962 6344 5918 5078 4834 10040 5200 (-5311) (-16703) 628 3509 4651 0 0)) (.split (.certified (weightedMixedLeafCap0Cap1SidePosSideNeg 5962 6882 6687 5816 5430 10602 5200 (-6588) (-16703) 1103 4242 2826 11669 0)) (.certified (weightedMixedLeafCap0Cap1SidePosSideNeg 5962 6749 6391 5548 5061 10457 5200 (-4673) (-16703) 47 3596 3228 13304 0))))
                    (.split (.certified (weightedMixedLeafCap0Cap1SidePosSideNeg 6628 6344 6978 4685 5115 10039 7374 (-5311) (-9669) 628 3676 3946 1789 0)) (.split (.split (.certified (weightedMixedLeafCap0Cap1SidePosSideNeg 6628 6006 6413 5624 6478 9725 7374 (-4521) (-9669) 1943 0 6421 8695 0)) (.certified (weightedMixedLeafCap0Cap1SidePosSideNeg 6628 7646 9073 5420 5114 11100 7374 (-11669) (-9669) 182 4758 1586 10843 0))) (.certified (weightedMixedLeafCap0Cap1SidePosSideNeg 6628 6749 7450 5133 5423 10428 7374 (-4673) (-9669) 47 4527 2390 13015 0)))))))
              (.split
                (.split
                  (.certified (weightedMixedLeafCap0Cap1SidePosSideNeg 4827 7843 8887 7889 4184 9219 4171 14373 (-6929) (-4168) 0 0 2778 0))
                  (.split
                    (.split (.certified (weightedMixedLeafCap0Cap1SidePosSideNeg 5923 7719 9837 8751 5028 10892 5543 14781 (-15158) (-4013) 0 5753 6929 0)) (.split (.certified (weightedMixedLeafCap0Cap1SidePosSideNeg 5923 7552 9887 8057 4765 10514 5543 10528 (-15158) (-3206) 0 5391 4004 0)) (.certified (weightedMixedLeafCap0Cap1SidePosSideNeg 5923 7764 10008 8439 5010 10809 5543 19443 (-15158) (-5334) 0 5605 9585 0))))
                    (.split (.split (.certified (weightedMixedLeafCap0Cap1SidePosSideNeg 6534 7288 10120 7925 5362 9510 7942 10776 (-9071) (-3025) 0 6157 0 0)) (.certified (weightedMixedLeafCap0Cap1SidePosSideNeg 6534 7992 10629 9093 6270 10503 7942 21354 (-9071) (-4904) 0 6000 6501 0))) (.split (.certified (weightedMixedLeafCap0Cap1SidePosSideNeg 6534 7552 10410 7915 5580 9687 7942 10528 (-9071) (-3206) 0 5237 4356 0)) (.certified (weightedMixedLeafCap0Cap1SidePosSideNeg 6534 7764 10561 8300 5858 10005 7942 19443 (-9071) (-5334) 0 5589 9909 0))))))
                (.split
                  (.certified (weightedMixedLeafCap0Cap1SidePosSideNeg 4916 7843 8974 7620 4113 9109 4034 14373 (-7108) (-4168) 0 0 4168 0))
                  (.split
                    (.split
                      (.split
                        (.split (.split (.certified (weightedMixedLeafCap0Cap1SidePosSideNeg 5951 7714 9547 6875 3869 11004 5278 28136 (-16270) (-1816) 0 6676 0 0)) (.split (.certified (weightedMixedLeafCap0Cap1SidePosSideNeg 5610 7714 9183 6541 3504 10606 4692 28136 (-14422) (-1816) 0 0 0 0)) (.split (.certified (weightedMixedLeafCap0Cap1SidePosSideNeg 6116 7714 9666 6931 3990 11365 5040 28136 (-27074) (-1816) 0 5796 0 0)) (.certified (weightedMixedLeafCap0Cap1SidePosSideNeg 6537 7714 10146 6981 4470 11123 6084 28136 (-16734) (-1816) 0 5901 0 0))))) (.certified (weightedMixedLeafCap0Cap1SidePosSideNeg 5962 6677 9396 8483 5185 9253 5200 6786 (-16703) (-4354) 4400 1666 0 0)))
                        (.split (.certified (weightedMixedLeafCap0Cap1SidePosSideNeg 5962 8192 9628 7821 4061 11620 5200 (-140455) (-16703) (-3155) 3546 2319 9085 0)) (.certified (weightedMixedLeafCap0Cap1SidePosSideNeg 5962 7541 10010 9633 6228 10318 5200 10580 (-16703) (-7221) 0 5427 6041 0))))
                      (.split (.split (.split (.certified (weightedMixedLeafCap0Cap1SidePosSideNeg 5951 8010 9861 7047 4183 11272 5278 26672 (-16270) (-1956) 0 6311 9458 0)) (.split (.certified (weightedMixedLeafCap0Cap1SidePosSideNeg 5610 8010 9497 6704 3818 10873 4692 26672 (-14422) (-1956) 0 0 9230 0)) (.certified (weightedMixedLeafCap0Cap1SidePosSideNeg 6339 8010 10235 7150 4555 11523 5545 26672 (-20591) (-1956) 3769 1986 9338 0)))) (.certified (weightedMixedLeafCap0Cap1SidePosSideNeg 5962 6905 9673 8428 5347 9395 5200 6667 (-16703) (-4607) 4087 1397 7780 0))) (.certified (weightedMixedLeafCap0Cap1SidePosSideNeg 5962 7764 10055 8184 4943 10688 5200 19443 (-16703) (-5334) 4084 1795 11631 0))))
                    (.split
                      (.split
                        (.split
                          (.split
                            (.split (.certified (weightedMixedLeafCap0Cap1SidePosSideNeg 6254 7714 9916 6575 4287 10032 6775 28136 (-8508) (-1816) 0 0 0 0)) (.split (.certified (weightedMixedLeafCap0Cap1SidePosSideNeg 6824 7714 10485 7093 4850 10893 7536 28136 (-11841) (-1816) 0 5992 0 0)) (.split (.certified (weightedMixedLeafCap0Cap1SidePosSideNeg 7069 7641 10675 7018 5093 10518 9002 28569 (-9584) (-1788) 0 5926 0 0)) (.split (.certified (weightedMixedLeafCap0Cap1SidePosSideNeg 7069 7669 10791 6738 5161 10419 9002 20702 (-9584) (-1436) 0 5319 0 0)) (.certified (weightedMixedLeafCap0Cap1SidePosSideNeg 7069 7922 10883 7419 5352 10872 9002 40922 (-9584) (-2239) 0 5683 0 0))))))
                            (.split
                              (.certified (weightedMixedLeafCap0Cap1SidePosSideNeg 6307 7714 9958 6456 4314 9985 6570 28136 (-8769) (-1816) 0 0 0 0))
                              (.split
                                (.split (.certified (weightedMixedLeafCap0Cap1SidePosSideNeg 6867 7641 10439 6943 4791 10778 7280 28569 (-12357) (-1788) 0 5873 0 0)) (.split (.certified (weightedMixedLeafCap0Cap1SidePosSideNeg 6867 7669 10577 6692 4905 10702 7280 20702 (-12357) (-1436) 0 5439 0 0)) (.certified (weightedMixedLeafCap0Cap1SidePosSideNeg 6867 7922 10628 7343 5014 11120 7280 40922 (-12357) (-2239) 4220 1445 0 0))))
                                (.split (.split (.certified (weightedMixedLeafCap0Cap1SidePosSideNeg 7122 7520 10686 6570 5045 10261 8664 20943 (-9939) (-1406) 0 5259 0 0)) (.certified (weightedMixedLeafCap0Cap1SidePosSideNeg 7122 7777 10770 7252 5220 10710 8664 43582 (-9939) (-2155) 0 5635 0 0))) (.split (.certified (weightedMixedLeafCap0Cap1SidePosSideNeg 7122 7669 10843 6634 5200 10388 8664 20702 (-9939) (-1436) 0 5363 0 0)) (.split (.certified (weightedMixedLeafCap0Cap1SidePosSideNeg 7122 7960 10719 6765 5040 11110 8664 (-196303) (-9939) (-1634) 0 5506 0 0)) (.certified (weightedMixedLeafCap0Cap1SidePosSideNeg 7122 7781 10988 7812 5788 10443 8664 18888 (-9939) (-2888) 0 5332 0 0))))))))
                          (.split (.certified (weightedMixedLeafCap0Cap1SidePosSideNeg 6603 6677 9829 8427 6117 8438 7503 6786 (-9506) (-4354) 0 5913 0 0)) (.split (.certified (weightedMixedLeafCap0Cap1SidePosSideNeg 6307 6677 9599 8052 5747 8060 6570 6786 (-8769) (-4354) 0 0 0 0)) (.certified (weightedMixedLeafCap0Cap1SidePosSideNeg 7003 6677 10226 8594 6485 8797 7946 6786 (-10996) (-4354) 0 5459 0 0)))))
                        (.split
                          (.split
                            (.certified (weightedMixedLeafCap0Cap1SidePosSideNeg 6603 8192 10450 7915 5034 11135 7503 (-140455) (-9506) (-3155) 0 6219 8149 0))
                            (.split (.certified (weightedMixedLeafCap0Cap1SidePosSideNeg 6307 8192 10111 7562 4654 10734 6570 (-140455) (-8769) (-3155) 0 0 8028 0)) (.split (.certified (weightedMixedLeafCap0Cap1SidePosSideNeg 6867 8192 10664 8034 5176 11550 7280 (-140455) (-12357) (-3155) 3899 1700 8405 0)) (.split (.split (.split (.certified (weightedMixedLeafCap0Cap1SidePosSideNeg 7122 8040 10579 7289 4920 11359 8664 (-35310) (-9939) (-2137) 0 5412 3099 0)) (.certified (weightedMixedLeafCap0Cap1SidePosSideNeg 7122 8036 11076 8515 6103 10897 8664 34277 (-9939) (-3559) 4224 924 5535 0))) .outside) (.split (.split (.certified (weightedMixedLeafCap0Cap1SidePosSideNeg 7122 8154 10731 7294 5065 11440 8664 (-38233) (-9939) (-2237) 0 5272 4178 0)) (.certified (weightedMixedLeafCap0Cap1SidePosSideNeg 7122 8114 11191 8445 6165 10924 8664 31903 (-9939) (-3697) 0 5116 7625 0))) .outside)))))
                          (.split (.certified (weightedMixedLeafCap0Cap1SidePosSideNeg 6603 7541 10543 9536 7210 9546 7503 10580 (-9506) (-7221) 0 5044 5892 0)) (.split (.certified (weightedMixedLeafCap0Cap1SidePosSideNeg 6307 7541 10284 9156 6830 9163 6570 10580 (-8769) (-7221) 0 0 4105 0)) (.split (.certified (weightedMixedLeafCap0Cap1SidePosSideNeg 6867 7541 10838 9759 7350 10086 7280 10580 (-12357) (-7221) 4148 916 6078 0)) (.split (.split (.certified (weightedMixedLeafCap0Cap1SidePosSideNeg 7122 7443 10931 9631 7678 9627 8664 9590 (-9939) (-6379) 4441 380 6475 0)) .outside) (.split (.certified (weightedMixedLeafCap0Cap1SidePosSideNeg 7122 7471 10987 9495 7641 9584 8664 9362 (-9939) (-6654) 0 4602 6034 0)) .outside)))))))
                      (.split
                        (.split
                          (.split
                            (.split (.certified (weightedMixedLeafCap0Cap1SidePosSideNeg 6254 8010 10228 6688 4595 10281 6775 26672 (-8508) (-1956) 0 0 8413 0)) (.split (.certified (weightedMixedLeafCap0Cap1SidePosSideNeg 6824 8010 10798 7239 5159 11150 7536 26672 (-11841) (-1956) 0 5706 8780 0)) (.split (.split (.certified (weightedMixedLeafCap0Cap1SidePosSideNeg 7069 7819 10947 6803 5316 10546 9002 20486 (-9584) (-1472) 0 5373 0 0)) (.certified (weightedMixedLeafCap0Cap1SidePosSideNeg 7069 8067 11038 7478 5501 10994 9002 38732 (-9584) (-2336) 0 5558 8188 0))) (.certified (weightedMixedLeafCap0Cap1SidePosSideNeg 7069 8084 11142 7203 5549 10891 9002 26361 (-9584) (-1998) 0 5727 11487 0)))))
                            (.split
                              (.certified (weightedMixedLeafCap0Cap1SidePosSideNeg 6307 8010 10272 6573 4623 10237 6570 26672 (-8769) (-1956) 0 0 8510 0))
                              (.split
                                (.split (.split (.certified (weightedMixedLeafCap0Cap1SidePosSideNeg 6867 7819 10734 6771 5061 10834 7280 20486 (-12357) (-1472) 4346 1072 0 0)) (.split (.certified (weightedMixedLeafCap0Cap1SidePosSideNeg 6867 8111 10542 6903 4878 11500 7280 (-268323) (-12357) (-1721) 0 5357 4485 0)) (.certified (weightedMixedLeafCap0Cap1SidePosSideNeg 6867 7918 10879 7891 5548 10876 7280 18390 (-12357) (-3000) 0 5270 8229 0)))) (.split (.certified (weightedMixedLeafCap0Cap1SidePosSideNeg 6867 7970 10890 6852 5218 10967 7280 20291 (-12357) (-1515) 4339 998 8514 0)) (.certified (weightedMixedLeafCap0Cap1SidePosSideNeg 6867 8104 10913 7220 5265 11200 7280 36899 (-12357) (-2448) 4101 1273 10440 0))))
                                (.split
                                  (.split (.certified (weightedMixedLeafCap0Cap1SidePosSideNeg 7122 7819 10999 6701 5355 10517 8664 20486 (-9939) (-1472) 4685 659 0 0)) (.split (.certified (weightedMixedLeafCap0Cap1SidePosSideNeg 7122 8111 10876 6859 5197 11248 8664 (-268323) (-9939) (-1721) 0 5323 5237 0)) (.certified (weightedMixedLeafCap0Cap1SidePosSideNeg 7122 7918 11138 7841 5920 10549 8664 18390 (-9939) (-3000) 4465 768 7913 0))))
                                  (.split (.split (.certified (weightedMixedLeafCap0Cap1SidePosSideNeg 7122 8105 11066 6393 5422 11050 8664 52029 (-9939) (-975) 0 5292 9830 0)) (.certified (weightedMixedLeafCap0Cap1SidePosSideNeg 7122 7735 11104 7155 5701 10138 8664 12657 (-9939) (-2070) 4665 472 8108 0))) (.split (.certified (weightedMixedLeafCap0Cap1SidePosSideNeg 7122 8189 11041 6716 5370 11240 8664 (-406701) (-9939) (-1820) 0 5281 9595 0)) (.certified (weightedMixedLeafCap0Cap1SidePosSideNeg 7122 7915 11206 7572 5897 10437 8664 17950 (-9939) (-3130) 4437 689 9440 0))))))))
                          (.split (.certified (weightedMixedLeafCap0Cap1SidePosSideNeg 6603 6905 10087 8327 6246 8549 7503 6667 (-9506) (-4607) 0 5679 7680 0)) (.split (.certified (weightedMixedLeafCap0Cap1SidePosSideNeg 6307 6905 9864 7947 5884 8176 6570 6667 (-8769) (-4607) 0 0 6556 0)) (.certified (weightedMixedLeafCap0Cap1SidePosSideNeg 7003 6905 10483 8507 6620 8914 7946 6667 (-10996) (-4607) 0 5358 7032 0)))))
                        (.split
                          (.split (.certified (weightedMixedLeafCap0Cap1SidePosSideNeg 6603 8146 10628 7295 5051 10869 7503 (-371101) (-9506) (-3431) 0 5991 9978 0)) (.split (.certified (weightedMixedLeafCap0Cap1SidePosSideNeg 6307 8146 10306 6929 4699 10469 6570 (-371101) (-8769) (-3431) 0 0 9197 0)) (.split (.certified (weightedMixedLeafCap0Cap1SidePosSideNeg 6867 8146 10864 7466 5248 11321 7280 (-371101) (-12357) (-3431) 3844 1609 8809 0)) (.split (.certified (weightedMixedLeafCap0Cap1SidePosSideNeg 7122 8169 11121 7613 5601 11119 8664 (-266662) (-9939) (-3356) 4263 1074 9097 0)) .outside))))
                          (.split (.certified (weightedMixedLeafCap0Cap1SidePosSideNeg 6603 7171 10308 8695 6596 8908 7503 10036 (-9506) (-7964) 0 5488 6937 0)) (.split (.certified (weightedMixedLeafCap0Cap1SidePosSideNeg 6307 7171 10074 8314 6229 8533 6570 10036 (-8769) (-7964) 0 0 6994 0)) (.split (.certified (weightedMixedLeafCap0Cap1SidePosSideNeg 6867 7171 10619 8924 6766 9471 7280 10036 (-12357) (-7964) 4062 907 7118 0)) (.split (.split (.split (.certified (weightedMixedLeafCap0Cap1SidePosSideNeg 7122 7582 11056 8833 6963 9784 8664 11740 (-9939) (-5786) 4370 462 7832 0)) (.certified (weightedMixedLeafCap0Cap1SidePosSideNeg 7122 6991 10634 9274 7668 8777 8664 7571 (-9939) (-8356) 4681 172 8759 0))) .outside) .outside))))))))))))))))

end Bescovitch
