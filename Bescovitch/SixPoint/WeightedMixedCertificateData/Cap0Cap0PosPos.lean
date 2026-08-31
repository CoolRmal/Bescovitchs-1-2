/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import Bescovitch.SixPoint.WeightedMixedCertificateData.Basic

/-!
# Mixed weighted certificate data for chart `(0, 0, 1, 1)`

This generated tree covers cap choices `0, 0` and stereographic side signs `1, 1`.
Every numerical leaf stores exact integer numerators with common denominator `4096`.
-/

@[expose] public section

namespace Bescovitch

/-- Assemble one exact q12 leaf for chart `(0, 0, 1, 1)`. -/
def weightedMixedLeafCap0Cap0SidePosSidePos
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
/-- The exact mixed-certificate tree for chart `(0, 0, 1, 1)`. -/
def weightedMixedTreeCap0Cap0SidePosSidePos : WeightedMixedTree :=
  (.split
    (.split
      (.split
        (.split
          (.split
            (.split (.certified (weightedMixedLeafCap0Cap0SidePosSidePos 1775 4786 3323 10232 5459 8722 (-351) (-4168) (-8907) 14373 0 7889 0 5551)) (.split (.split (.certified (weightedMixedLeafCap0Cap0SidePosSidePos 2039 1886 543 10572 5139 5216 (-861) 549 (-7480) (-5392) 0 52769 0 25975)) (.certified (weightedMixedLeafCap0Cap0SidePosSidePos 2219 1886 808 10501 4991 5250 182 549 (-11669) (-5392) 0 2314 0 6637))) (.split (.certified (weightedMixedLeafCap0Cap0SidePosSidePos 1560 1886 937 10455 5247 4922 (-688) 549 (-7169) (-5392) 0 22429 0 17724)) (.certified (weightedMixedLeafCap0Cap0SidePosSidePos 1961 1886 1023 10191 4698 4939 298 549 (-11384) (-5392) 0 0 0 14343)))))
            (.split (.certified (weightedMixedLeafCap0Cap0SidePosSidePos 1775 1886 1198 7871 4493 5773 (-351) (-549) (-8907) 5392 0 4756 0 3298)) (.certified (weightedMixedLeafCap0Cap0SidePosSidePos 1775 4786 2666 11449 5771 6814 (-351) 4168 (-8907) (-14373) 0 568 0 5393))))
          (.split (.split (.certified (weightedMixedLeafCap0Cap0SidePosSidePos 1775 4753 3596 9917 4955 8767 (-351) (-3651) (-8907) 16396 0 7660 1 5839)) (.certified (weightedMixedLeafCap0Cap0SidePosSidePos 1775 1802 1211 9881 4530 4487 (-351) 827 (-8907) (-5039) 0 11998 0 0))) (.split (.certified (weightedMixedLeafCap0Cap0SidePosSidePos 1775 1802 1823 7457 3866 5842 (-351) (-827) (-8907) 5039 0 3867 0 527)) (.certified (weightedMixedLeafCap0Cap0SidePosSidePos 1775 4753 2859 10888 5218 6406 (-351) 3651 (-8907) (-16396) 0 967 0 6243)))))
        (.split
          (.split (.split (.certified (weightedMixedLeafCap0Cap0SidePosSidePos 2568 4786 2405 7436 6628 7474 1326 (-4168) (-3750) 14373 0 0 0 5682)) (.certified (weightedMixedLeafCap0Cap0SidePosSidePos 2568 1886 2048 9305 4091 3695 1326 549 (-3750) (-5392) 0 0 0 372))) (.split (.certified (weightedMixedLeafCap0Cap0SidePosSidePos 2568 1886 795 4828 6227 4887 1326 (-549) (-3750) 5392 0 0 0 16820)) (.certified (weightedMixedLeafCap0Cap0SidePosSidePos 2568 4786 4396 9482 5645 4121 1326 4168 (-3750) (-14373) 0 0 0 4503))))
          (.split
            (.split (.certified (weightedMixedLeafCap0Cap0SidePosSidePos 2568 4753 2352 7224 6044 7739 1326 (-3651) (-3750) 16396 0 0 0 6940)) (.certified (weightedMixedLeafCap0Cap0SidePosSidePos 2568 1802 2602 8680 3490 3090 1326 827 (-3750) (-5039) 0 0 0 227)))
            (.split (.split (.certified (weightedMixedLeafCap0Cap0SidePosSidePos 2871 1802 2048 4881 5763 5421 1231 (-827) (-3801) 5039 0 0 0 571)) (.split (.certified (weightedMixedLeafCap0Cap0SidePosSidePos 2219 1802 1051 4037 5409 5182 968 (-827) (-3134) 5039 0 0 690 2510)) (.split (.certified (weightedMixedLeafCap0Cap0SidePosSidePos 2955 1802 2048 5735 5903 5259 1665 (-827) (-5288) 5039 0 0 0 2063)) (.certified (weightedMixedLeafCap0Cap0SidePosSidePos 3649 1802 896 4566 6562 4961 2491 (-827) (-3828) 5039 0 0 4005 10768))))) (.certified (weightedMixedLeafCap0Cap0SidePosSidePos 2568 4753 4680 8870 5226 3589 1326 3651 (-3750) (-16396) 0 0 0 5625))))))
      (.split
        (.split
          (.split (.split (.certified (weightedMixedLeafCap0Cap0SidePosSidePos 3812 4786 3165 11696 7868 8663 2657 (-4168) (-69408) 14373 0 8914 0 2841)) (.certified (weightedMixedLeafCap0Cap0SidePosSidePos 3812 1886 2938 10208 4541 5810 2657 549 (-69408) (-5392) 0 7498 0 0))) (.split (.certified (weightedMixedLeafCap0Cap0SidePosSidePos 3812 1886 1754 9835 7414 5913 2657 (-549) (-69408) 5392 0 12753 0 11965)) (.certified (weightedMixedLeafCap0Cap0SidePosSidePos 3812 4786 5579 11870 6566 8394 2657 4168 (-69408) (-14373) 0 8516 0 4622))))
          (.split
            (.split (.certified (weightedMixedLeafCap0Cap0SidePosSidePos 3812 4753 2871 11260 7280 8496 2657 (-3651) (-69408) 16396 0 11060 0 10238)) (.certified (weightedMixedLeafCap0Cap0SidePosSidePos 3812 1802 3357 9656 4015 5471 2657 827 (-69408) (-5039) 0 6322 0 0)))
            (.split (.split (.split (.certified (weightedMixedLeafCap0Cap0SidePosSidePos 3258 1802 2048 8908 6075 5722 1956 (-827) (-26672) 5039 0 0 0 6216)) (.split (.certified (weightedMixedLeafCap0Cap0SidePosSidePos 3084 1802 2048 9575 5984 5587 2664 (-827) 30930 5039 0 21022 1080 5149)) (.certified (weightedMixedLeafCap0Cap0SidePosSidePos 4047 1802 1190 8675 6862 5862 4311 (-827) (-39721) 5039 0 32259 2169 9529)))) (.split (.certified (weightedMixedLeafCap0Cap0SidePosSidePos 3088 1802 2048 8679 6036 5409 1816 (-827) (-28136) 5039 0 0 0 7077)) (.certified (weightedMixedLeafCap0Cap0SidePosSidePos 4140 1802 1590 9525 7201 5616 3155 (-827) 140455 5039 0 16025 0 11390)))) (.certified (weightedMixedLeafCap0Cap0SidePosSidePos 3812 4753 5810 11398 6214 8162 2657 3651 (-69408) (-16396) 0 9189 0 7372)))))
        (.split
          (.split (.split (.certified (weightedMixedLeafCap0Cap0SidePosSidePos 5460 4786 5026 10079 9499 8680 6029 (-4168) (-8320) 14373 0 4212 0 2494)) (.certified (weightedMixedLeafCap0Cap0SidePosSidePos 5460 1886 3913 10464 6297 4976 6029 549 (-8320) (-5392) 0 6813 0 0))) (.split (.certified (weightedMixedLeafCap0Cap0SidePosSidePos 5460 1886 3107 7692 8638 5736 6029 (-549) (-8320) 5392 0 7169 0 5469)) (.certified (weightedMixedLeafCap0Cap0SidePosSidePos 5460 4786 6838 11364 8432 6664 6029 4168 (-8320) (-14373) 0 5218 0 6364))))
          (.split (.split (.certified (weightedMixedLeafCap0Cap0SidePosSidePos 5460 4753 4695 9773 8937 8741 6029 (-3651) (-8320) 16396 0 9722 0 2425)) (.certified (weightedMixedLeafCap0Cap0SidePosSidePos 5460 1802 4072 9846 5813 4400 6029 827 (-8320) (-5039) 0 6368 0 0))) (.split (.certified (weightedMixedLeafCap0Cap0SidePosSidePos 5460 1802 2536 7286 8016 5828 6029 (-827) (-8320) 5039 0 11481 0 4185)) (.certified (weightedMixedLeafCap0Cap0SidePosSidePos 5460 4753 6930 10798 8077 6245 6029 3651 (-8320) (-16396) 0 8377 0 6624)))))))
    (.split
      (.split
        (.split
          (.split (.split (.certified (weightedMixedLeafCap0Cap0SidePosSidePos 1178 4786 2795 9656 5047 8106 (-80) (-4168) (-8188) 14373 0 7343 0 8954)) (.certified (weightedMixedLeafCap0Cap0SidePosSidePos 1178 1886 1258 9887 4617 4425 (-80) 549 (-8188) (-5392) 0 1020 0 16955))) (.split (.certified (weightedMixedLeafCap0Cap0SidePosSidePos 1178 1886 1368 7359 4420 5160 (-80) (-549) (-8188) 5392 0 676 0 2511)) (.certified (weightedMixedLeafCap0Cap0SidePosSidePos 1178 4786 2592 10821 5143 6238 (-80) 4168 (-8188) (-14373) 0 0 0 5815))))
          (.split (.split (.certified (weightedMixedLeafCap0Cap0SidePosSidePos 1178 4753 3134 9328 4511 8162 (-80) (-3651) (-8188) 16396 0 9015 0 7328)) (.certified (weightedMixedLeafCap0Cap0SidePosSidePos 1178 1802 1834 9270 3995 3859 (-80) 827 (-8188) (-5039) 0 1853 0 8853))) (.split (.certified (weightedMixedLeafCap0Cap0SidePosSidePos 1178 1802 1970 6924 3796 5248 (-80) (-827) (-8188) 5039 0 3073 0 0)) (.certified (weightedMixedLeafCap0Cap0SidePosSidePos 1178 4753 2916 10260 4593 5851 (-80) 3651 (-8188) (-16396) 0 0 0 9527)))))
        (.split
          (.split (.split (.certified (weightedMixedLeafCap0Cap0SidePosSidePos 2817 4786 2052 7132 6829 6867 1632 (-4168) (-3510) 14373 0 0 0 3312)) (.certified (weightedMixedLeafCap0Cap0SidePosSidePos 2817 1886 2667 8699 3602 3071 1632 549 (-3510) (-5392) 0 0 0 0))) (.split (.certified (weightedMixedLeafCap0Cap0SidePosSidePos 2817 1886 1422 4674 6667 4259 1632 (-549) (-3510) 5392 0 0 0 9490)) (.certified (weightedMixedLeafCap0Cap0SidePosSidePos 2817 4786 4853 8962 5423 3751 1632 4168 (-3510) (-14373) 0 0 0 4695))))
          (.split (.split (.split (.certified (weightedMixedLeafCap0Cap0SidePosSidePos 2743 4753 1980 6959 6175 7275 1565 (-3651) (-3575) 16396 0 0 0 6204)) (.split (.certified (weightedMixedLeafCap0Cap0SidePosSidePos 2305 4753 1299 6170 5598 6865 1260 (-3651) (-2858) 16396 0 2657 0 5270)) (.certified (weightedMixedLeafCap0Cap0SidePosSidePos 3544 4753 2364 7442 6975 7143 2287 (-3651) (-4273) 16396 0 0 0 924)))) (.certified (weightedMixedLeafCap0Cap0SidePosSidePos 2817 1802 3229 8074 3025 2463 1632 827 (-3510) (-5039) 0 0 0 0))) (.split (.certified (weightedMixedLeafCap0Cap0SidePosSidePos 2817 1802 1137 4274 6048 4657 1632 (-827) (-3510) 5039 0 0 4342 8528)) (.certified (weightedMixedLeafCap0Cap0SidePosSidePos 2817 4753 5183 8356 5059 3272 1632 3651 (-3510) (-16396) 0 0 0 6010))))))
      (.split
        (.split
          (.split (.split (.certified (weightedMixedLeafCap0Cap0SidePosSidePos 3573 4786 2606 11196 7589 8042 2288 (-4168) (-156699) 14373 0 10110 0 12909)) (.certified (weightedMixedLeafCap0Cap0SidePosSidePos 3573 1886 3133 9580 3917 5273 2288 549 (-156699) (-5392) 0 9994 0 3373))) (.split (.certified (weightedMixedLeafCap0Cap0SidePosSidePos 3573 1886 1874 9430 7370 5317 2288 (-549) (-156699) 5392 0 12734 0 11437)) (.certified (weightedMixedLeafCap0Cap0SidePosSidePos 3573 4786 5544 11265 6022 7933 2288 4168 (-156699) (-14373) 4035 3101 0 9198))))
          (.split
            (.split
              (.split
                (.split (.certified (weightedMixedLeafCap0Cap0SidePosSidePos 2942 4753 2318 10463 6405 7997 1712 (-3651) (-30082) 16396 0 0 0 12482)) (.split (.certified (weightedMixedLeafCap0Cap0SidePosSidePos 3598 4753 2018 11319 6958 7679 2239 (-3651) 23814 16396 0 7864 5536 4589)) (.certified (weightedMixedLeafCap0Cap0SidePosSidePos 4959 4753 3447 11176 8393 8434 3699 (-3651) (-63830) 16396 0 8894 5947 3502))))
                (.split
                  (.split (.certified (weightedMixedLeafCap0Cap0SidePosSidePos 2169 4753 2036 10382 5625 7447 1083 (-3651) (-1126501) 16396 0 0 2635 1445)) (.certified (weightedMixedLeafCap0Cap0SidePosSidePos 3455 4753 2301 9915 6884 7809 2200 (-3651) (-16880) 16396 0 0 0 12272)))
                  (.split (.split (.certified (weightedMixedLeafCap0Cap0SidePosSidePos 3470 4754 1800 11172 6928 7433 2077 (-3757) 20873 15779 0 8731 0 9618)) (.split (.certified (weightedMixedLeafCap0Cap0SidePosSidePos 3470 5495 2301 11387 6818 7979 2077 (-4291) 20873 27947 0 7052 987 154)) (.certified (weightedMixedLeafCap0Cap0SidePosSidePos 3470 4021 1044 10488 6502 6632 2077 (-2789) 20873 11472 876 11115 0 0)))) (.split (.certified (weightedMixedLeafCap0Cap0SidePosSidePos 4924 4754 3354 11074 8476 8173 3476 (-3757) (-100712) 15779 1726 3789 0 10506)) (.split (.certified (weightedMixedLeafCap0Cap0SidePosSidePos 4924 5495 3692 11404 8406 8821 3476 (-4291) (-100712) 27947 2693 4672 5452 3288)) (.certified (weightedMixedLeafCap0Cap0SidePosSidePos 4924 4021 2649 10331 8003 7380 3476 (-2789) (-100712) 11472 3053 1369 0 0)))))))
              (.certified (weightedMixedLeafCap0Cap0SidePosSidePos 3573 1802 3628 9029 3400 4969 2288 827 (-156699) (-5039) 4625 4520 0 0)))
            (.split
              (.split
                (.split
                  (.split
                    (.split (.split (.certified (weightedMixedLeafCap0Cap0SidePosSidePos 2369 2540 2048 9373 5539 5691 1157 (-1324) (-278519) 6344 0 0 0 0)) (.certified (weightedMixedLeafCap0Cap0SidePosSidePos 2369 1067 1414 8623 5715 4346 1157 (-361) (-278519) 4324 0 0 0 12832))) (.split (.certified (weightedMixedLeafCap0Cap0SidePosSidePos 2369 2549 2048 9116 5225 5586 1157 (-1400) (-278519) 6193 0 0 0 0)) (.certified (weightedMixedLeafCap0Cap0SidePosSidePos 2369 1087 1479 8343 5411 4207 1157 (-488) (-278519) 4126 0 0 4011 8169))))
                    (.split (.certified (weightedMixedLeafCap0Cap0SidePosSidePos 3505 1803 1121 8110 6699 5190 2290 (-767) (-16100) 5135 0 0 0 15276)) (.split (.certified (weightedMixedLeafCap0Cap0SidePosSidePos 3505 2549 724 8373 6370 5901 2290 (-1400) (-16100) 6193 0 0 0 0)) (.certified (weightedMixedLeafCap0Cap0SidePosSidePos 3505 1087 1421 7408 6486 4427 2290 (-488) (-16100) 4126 0 0 2763 9736)))))
                  (.certified (weightedMixedLeafCap0Cap0SidePosSidePos 4325 1802 1965 9560 7489 5414 2929 (-827) 82331 5039 0 13437 0 9336)))
                (.split (.split (.certified (weightedMixedLeafCap0Cap0SidePosSidePos 2169 1802 1047 8589 5348 4633 1083 (-827) (-1126501) 5039 0 0 7435 9271)) (.split (.certified (weightedMixedLeafCap0Cap0SidePosSidePos 3455 1803 1311 7933 6753 4882 2200 (-767) (-16880) 5135 0 0 0 13753)) (.split (.split (.certified (weightedMixedLeafCap0Cap0SidePosSidePos 3455 3544 1101 7167 6036 6577 2200 (-2287) (-16880) 4273 0 0 0 0)) (.certified (weightedMixedLeafCap0Cap0SidePosSidePos 3455 1511 1716 9159 6541 4595 2200 (-456) (-16880) 10697 0 0 0 0))) (.certified (weightedMixedLeafCap0Cap0SidePosSidePos 3455 1087 1712 7245 6576 4116 2200 (-488) (-16880) 4126 0 0 2440 8641))))) (.certified (weightedMixedLeafCap0Cap0SidePosSidePos 4245 1802 2082 9368 7484 5120 2742 (-827) 55899 5039 0 12208 0 9025))))
              (.split (.split (.certified (weightedMixedLeafCap0Cap0SidePosSidePos 2942 4753 5089 10743 5428 7309 1712 3651 (-30082) (-16396) 0 0 0 7965)) (.certified (weightedMixedLeafCap0Cap0SidePosSidePos 4325 4753 6561 11201 6286 8400 2929 3651 82331 (-16396) 0 7939 0 7677))) (.split (.certified (weightedMixedLeafCap0Cap0SidePosSidePos 2824 4753 5125 10439 5157 7086 1632 3651 (-32793) (-16396) 0 0 0 8313)) (.split (.certified (weightedMixedLeafCap0Cap0SidePosSidePos 3470 4753 5961 10621 5246 8403 2077 3651 20873 (-16396) 0 6930 0 6245)) (.certified (weightedMixedLeafCap0Cap0SidePosSidePos 4924 4753 7098 11054 6843 7915 3476 3651 (-100712) (-16396) 4397 2867 0 6857))))))))
        (.split
          (.split (.split (.certified (weightedMixedLeafCap0Cap0SidePosSidePos 5581 4786 4867 9857 9640 8163 5246 (-4168) (-9059) 14373 0 4295 0 7448)) (.certified (weightedMixedLeafCap0Cap0SidePosSidePos 5581 1886 4269 9930 5991 4533 5246 549 (-9059) (-5392) 0 6766 0 0))) (.split (.certified (weightedMixedLeafCap0Cap0SidePosSidePos 5581 1886 3324 7596 8960 5212 5246 (-549) (-9059) 5392 0 6886 0 6277)) (.certified (weightedMixedLeafCap0Cap0SidePosSidePos 5581 4786 7140 10934 8285 6441 5246 4168 (-9059) (-14373) 0 5143 0 8580))))
          (.split
            (.split
              (.split
                (.split (.certified (weightedMixedLeafCap0Cap0SidePosSidePos 4827 4753 3830 8905 8307 7980 4171 (-3651) (-6929) 16396 0 0 0 1791)) (.certified (weightedMixedLeafCap0Cap0SidePosSidePos 6266 4753 5223 10263 9748 8734 6658 (-3651) (-11263) 16396 0 8767 0 8049)))
                (.split
                  (.certified (weightedMixedLeafCap0Cap0SidePosSidePos 4916 4753 3721 8778 8385 7699 4034 (-3651) (-7108) 16396 0 0 0 9995))
                  (.split (.split (.certified (weightedMixedLeafCap0Cap0SidePosSidePos 5962 4754 4708 10566 9577 8458 5200 (-3757) (-16703) 15779 0 6976 0 9312)) (.split (.certified (weightedMixedLeafCap0Cap0SidePosSidePos 5962 5495 5073 10988 9577 9175 5200 (-4291) (-16703) 27947 4420 2724 5620 2111)) (.certified (weightedMixedLeafCap0Cap0SidePosSidePos 5962 4021 3971 9790 9041 7701 5200 (-2789) (-16703) 11472 3580 1011 0 0)))) (.split (.certified (weightedMixedLeafCap0Cap0SidePosSidePos 6628 4754 5696 9897 10251 8447 7374 (-3757) (-9669) 15779 3343 1539 0 8211)) (.split (.certified (weightedMixedLeafCap0Cap0SidePosSidePos 6628 5495 6118 10382 10319 9206 7374 (-4291) (-9669) 27947 0 7450 0 6372)) (.certified (weightedMixedLeafCap0Cap0SidePosSidePos 6628 4021 4928 9105 9662 7737 7374 (-2789) (-9669) 11472 3521 1160 0 0)))))))
              (.certified (weightedMixedLeafCap0Cap0SidePosSidePos 5581 1802 4498 9316 5547 3985 5246 827 (-9059) (-5039) 4344 1999 0 0)))
            (.split
              (.certified (weightedMixedLeafCap0Cap0SidePosSidePos 5581 1802 2711 7152 8334 5268 5246 (-827) (-9059) 5039 0 10914 0 4889))
              (.split
                (.split (.certified (weightedMixedLeafCap0Cap0SidePosSidePos 4827 4753 6596 9938 7263 5397 4171 3651 (-6929) (-16396) 0 0 0 6336)) (.split (.certified (weightedMixedLeafCap0Cap0SidePosSidePos 5923 4753 7634 11218 8251 7258 5543 3651 (-15158) (-16396) 0 7131 5716 789)) (.split (.certified (weightedMixedLeafCap0Cap0SidePosSidePos 6534 4754 7893 10978 9185 6493 7942 3757 (-9071) (-15779) 0 6990 0 6845)) (.split (.certified (weightedMixedLeafCap0Cap0SidePosSidePos 6534 4021 7206 10371 8392 5724 7942 2789 (-9071) (-11472) 0 5780 0 0)) (.certified (weightedMixedLeafCap0Cap0SidePosSidePos 6534 5495 8664 11069 9674 6908 7942 4291 (-9071) (-27947) 0 6520 5140 226))))))
                (.split
                  (.certified (weightedMixedLeafCap0Cap0SidePosSidePos 4916 4753 6796 9723 7218 5314 4034 3651 (-7108) (-16396) 0 0 0 6368))
                  (.split
                    (.split (.certified (weightedMixedLeafCap0Cap0SidePosSidePos 5962 4754 7732 11127 8238 7236 5200 3757 (-16703) (-15779) 4174 1221 0 7808)) (.split (.certified (weightedMixedLeafCap0Cap0SidePosSidePos 5962 4021 7127 10456 7437 6438 5200 2789 (-16703) (-11472) 3859 1299 0 0)) (.split (.certified (weightedMixedLeafCap0Cap0SidePosSidePos 5962 4245 7509 11148 9450 6254 5200 2742 (-16703) 55899 4687 1196 3956 2645)) (.certified (weightedMixedLeafCap0Cap0SidePosSidePos 5962 6335 9097 11102 7955 8896 5200 6220 (-16703) (-12141) 4593 1464 4796 653)))))
                    (.split
                      (.split (.certified (weightedMixedLeafCap0Cap0SidePosSidePos 6628 4016 7351 10473 8544 5867 7374 2891 (-9669) (-11083) 4850 811 0 0)) (.certified (weightedMixedLeafCap0Cap0SidePosSidePos 6628 5491 8811 11184 9828 7059 7374 4565 (-9669) (-24011) 4782 742 0 6593)))
                      (.split
                        (.certified (weightedMixedLeafCap0Cap0SidePosSidePos 6628 4021 7407 10190 8382 5669 7374 2789 (-9669) (-11472) 4920 627 0 0))
                        (.split
                          (.certified (weightedMixedLeafCap0Cap0SidePosSidePos 6628 4245 7700 10591 10236 5390 7374 2742 (-9669) 55899 5763 846 3314 2660))
                          (.split (.certified (weightedMixedLeafCap0Cap0SidePosSidePos 6603 6335 9509 10885 8930 8085 7503 6220 (-9506) (-12141) 0 6026 4719 566)) (.split (.certified (weightedMixedLeafCap0Cap0SidePosSidePos 6307 6335 9285 10493 8553 7705 6570 6220 (-8769) (-12141) 0 0 3858 1331)) (.split (.certified (weightedMixedLeafCap0Cap0SidePosSidePos 6867 6335 9826 11170 9076 8639 7280 6220 (-12357) (-12141) 4594 947 4973 314)) (.split (.certified (weightedMixedLeafCap0Cap0SidePosSidePos 7122 6316 9939 11080 9500 8266 8664 6320 (-9939) (-11899) 4380 448 0 5875)) (.split (.certified (weightedMixedLeafCap0Cap0SidePosSidePos 7122 5998 9656 10705 9106 7871 8664 5585 (-9939) (-10828) 4720 335 0 0)) (.certified (weightedMixedLeafCap0Cap0SidePosSidePos 7122 6712 10340 11245 9828 8591 8664 6661 (-9939) (-14177) 4721 222 4863 359)))))))))))))))))))

end Bescovitch
