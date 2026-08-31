/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import Bescovitch.SixPoint.WeightedMixedCertificateData.Basic

/-!
# Mixed weighted certificate data for chart `(0, 0, 1, -1)`

This generated tree covers cap choices `0, 0` and stereographic side signs `1, -1`.
Every numerical leaf stores exact integer numerators with common denominator `4096`.
-/

@[expose] public section

namespace Bescovitch

/-- Assemble one exact q12 leaf for chart `(0, 0, 1, -1)`. -/
def weightedMixedLeafCap0Cap0SidePosSideNeg
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
/-- The exact mixed-certificate tree for chart `(0, 0, 1, -1)`. -/
def weightedMixedTreeCap0Cap0SidePosSideNeg : WeightedMixedTree :=
  (.split
    (.split
      (.split
        (.split
          (.split (.split (.certified (weightedMixedLeafCap0Cap0SidePosSideNeg 1775 6446 4178 5711 3560 9790 (-351) (-30584) (-8907) 3112 0 1896 0 5441)) (.certified (weightedMixedLeafCap0Cap0SidePosSideNeg 1775 4713 2611 6171 3077 6731 (-351) 4025 (-8907) (-1167) 0 3357 0 4889))) (.split (.certified (weightedMixedLeafCap0Cap0SidePosSideNeg 1775 4713 3279 3421 2442 8656 (-351) (-4025) (-8907) 1167 0 12701 0 9112)) (.certified (weightedMixedLeafCap0Cap0SidePosSideNeg 1775 6446 4053 8990 4367 9383 (-351) 30584 (-8907) (-3112) 0 7194 0 4285))))
          (.split (.split (.certified (weightedMixedLeafCap0Cap0SidePosSideNeg 1775 6886 4685 6036 3167 10334 (-351) (-20286) (-8907) 3329 0 1889 0 4269)) (.certified (weightedMixedLeafCap0Cap0SidePosSideNeg 1775 5299 3238 5976 2450 7075 (-351) 4595 (-8907) (-1023) 0 3403 0 4470))) (.split (.certified (weightedMixedLeafCap0Cap0SidePosSideNeg 1775 5299 3904 3940 1822 9268 (-351) (-4595) (-8907) 1023 0 12190 0 8646)) (.certified (weightedMixedLeafCap0Cap0SidePosSideNeg 1775 6886 4482 8857 3951 9633 (-351) 20286 (-8907) (-3329) 0 6640 0 2380)))))
        (.split
          (.split (.split (.certified (weightedMixedLeafCap0Cap0SidePosSideNeg 2568 6446 4534 2653 5424 7653 1326 (-30584) (-3750) 3112 0 0 0 10236)) (.certified (weightedMixedLeafCap0Cap0SidePosSideNeg 2568 4713 4355 6191 1493 4044 1326 4025 (-3750) (-1167) 0 0 0 5854))) (.split (.certified (weightedMixedLeafCap0Cap0SidePosSideNeg 2568 4713 2329 1926 3780 7432 1326 (-4025) (-3750) 1167 0 0 0 11309)) (.certified (weightedMixedLeafCap0Cap0SidePosSideNeg 2568 6446 4911 8385 2718 6952 1326 30584 (-3750) (-3112) 0 0 0 4192))))
          (.split (.split (.certified (weightedMixedLeafCap0Cap0SidePosSideNeg 2568 6886 4852 3092 5027 8260 1326 (-20286) (-3750) 3329 0 0 0 11382)) (.certified (weightedMixedLeafCap0Cap0SidePosSideNeg 2568 5299 4978 5720 953 4229 1326 4595 (-3750) (-1023) 0 0 0 7721))) (.split (.certified (weightedMixedLeafCap0Cap0SidePosSideNeg 2568 5299 2899 2497 3183 8055 1326 (-4595) (-3750) 1023 0 4676 0 8711)) (.certified (weightedMixedLeafCap0Cap0SidePosSideNeg 2568 6886 5471 8044 2462 7061 1326 20286 (-3750) (-3329) 0 0 0 3832))))))
      (.split
        (.split
          (.split (.split (.certified (weightedMixedLeafCap0Cap0SidePosSideNeg 3812 6446 5656 7832 6434 10506 2657 (-30584) (-69408) 3112 0 7620 0 4401)) (.certified (weightedMixedLeafCap0Cap0SidePosSideNeg 3812 4713 5532 5360 2048 8312 2657 4025 (-69408) (-1167) 0 7798 0 9056))) (.split (.certified (weightedMixedLeafCap0Cap0SidePosSideNeg 3812 4713 3081 4964 4348 8583 2657 (-4025) (-69408) 1167 0 6295 0 0)) (.certified (weightedMixedLeafCap0Cap0SidePosSideNeg 3812 6446 6127 8295 2656 10448 2657 30584 (-69408) (-3112) 0 9828 0 6107))))
          (.split
            (.split (.certified (weightedMixedLeafCap0Cap0SidePosSideNeg 3812 6886 5908 7974 6098 10943 2657 (-20286) (-69408) 3329 0 9146 0 2910)) (.split (.certified (weightedMixedLeafCap0Cap0SidePosSideNeg 3580 5299 5828 5614 2048 8679 2782 4595 (-62225) (-1023) 0 10738 0 5896)) (.split (.certified (weightedMixedLeafCap0Cap0SidePosSideNeg 3088 5299 5409 5303 2048 8188 1816 4595 (-28136) (-1023) 0 0 0 6303)) (.certified (weightedMixedLeafCap0Cap0SidePosSideNeg 4140 5299 6574 5382 1018 9001 3155 4595 140455 (-1023) 0 14605 0 7175)))))
            (.split (.certified (weightedMixedLeafCap0Cap0SidePosSideNeg 3812 5299 3523 5186 3833 9114 2657 (-4595) (-69408) 1023 0 8710 0 0)) (.split (.certified (weightedMixedLeafCap0Cap0SidePosSideNeg 3580 6886 6492 8534 2865 10800 2782 20286 (-62225) (-3329) 0 10075 0 8833)) (.split (.certified (weightedMixedLeafCap0Cap0SidePosSideNeg 3088 6886 5996 8243 2624 10338 1816 20286 (-28136) (-3329) 0 0 8457 1136)) (.split (.certified (weightedMixedLeafCap0Cap0SidePosSideNeg 3488 6886 6321 7765 2140 10976 2431 20286 27142 (-3329) 0 6833 3725 0)) (.certified (weightedMixedLeafCap0Cap0SidePosSideNeg 4715 6886 7590 8560 3152 10779 3973 20286 (-48279) (-3329) 0 8305 8154 399))))))))
        (.split
          (.split (.split (.certified (weightedMixedLeafCap0Cap0SidePosSideNeg 5460 6446 7475 5527 7275 9689 6029 (-30584) (-8320) 3112 0 8440 0 4117)) (.certified (weightedMixedLeafCap0Cap0SidePosSideNeg 5460 4713 6776 6201 1535 6580 6029 4025 (-8320) (-1167) 0 8559 0 8016))) (.split (.certified (weightedMixedLeafCap0Cap0SidePosSideNeg 5460 4713 4942 3303 4635 8616 6029 (-4025) (-8320) 1167 0 4038 0 0)) (.certified (weightedMixedLeafCap0Cap0SidePosSideNeg 5460 6446 7844 8993 4239 9259 6029 30584 (-8320) (-3112) 0 9008 0 2292))))
          (.split
            (.split (.certified (weightedMixedLeafCap0Cap0SidePosSideNeg 5460 6886 7756 5863 7077 10239 6029 (-20286) (-8320) 3329 0 8123 0 2763)) (.certified (weightedMixedLeafCap0Cap0SidePosSideNeg 5460 5299 7395 5984 2000 6914 6029 4595 (-8320) (-1023) 0 9758 0 4859)))
            (.split (.certified (weightedMixedLeafCap0Cap0SidePosSideNeg 5460 5299 5358 3839 4317 9230 6029 (-4595) (-8320) 1023 0 6004 0 1244)) (.split (.certified (weightedMixedLeafCap0Cap0SidePosSideNeg 5090 6886 8015 8846 4222 9271 6311 20286 (-8180) (-3329) 0 9063 0 3147)) (.split (.certified (weightedMixedLeafCap0Cap0SidePosSideNeg 4758 6886 7677 8411 3726 8780 4354 20286 (-6786) (-3329) 0 0 1601 0)) (.split (.certified (weightedMixedLeafCap0Cap0SidePosSideNeg 5595 6886 8510 8872 4261 10177 5976 20286 (-14008) (-3329) 0 8354 0 7733)) (.certified (weightedMixedLeafCap0Cap0SidePosSideNeg 6155 6886 9080 8870 5126 9425 8686 20286 (-8595) (-3329) 0 7943 0 7233))))))))))
    (.split
      (.split
        (.split
          (.split (.split (.certified (weightedMixedLeafCap0Cap0SidePosSideNeg 1178 6446 3571 5218 3798 9165 (-80) (-30584) (-8188) 3112 0 0 0 2959)) (.certified (weightedMixedLeafCap0Cap0SidePosSideNeg 1178 4713 2554 5634 3204 6154 (-80) 4025 (-8188) (-1167) 0 0 0 1483))) (.split (.certified (weightedMixedLeafCap0Cap0SidePosSideNeg 1178 4713 2760 2810 3048 8041 (-80) (-4025) (-8188) 1167 0 10387 0 14303)) (.certified (weightedMixedLeafCap0Cap0SidePosSideNeg 1178 6446 3531 8416 4026 8772 (-80) 30584 (-8188) (-3112) 0 3176 0 10733))))
          (.split (.split (.certified (weightedMixedLeafCap0Cap0SidePosSideNeg 1178 6886 4066 5508 3327 9708 (-80) (-20286) (-8188) 3329 0 0 0 1360)) (.certified (weightedMixedLeafCap0Cap0SidePosSideNeg 1178 5299 3173 5408 2584 6520 (-80) 4595 (-8188) (-1023) 0 0 0 1648))) (.split (.certified (weightedMixedLeafCap0Cap0SidePosSideNeg 1178 5299 3375 3317 2436 8655 (-80) (-4595) (-8188) 1023 0 13387 0 6822)) (.certified (weightedMixedLeafCap0Cap0SidePosSideNeg 1178 6886 4002 8266 3552 9033 (-80) 20286 (-8188) (-3329) 0 5838 0 4278)))))
        (.split
          (.split (.split (.certified (weightedMixedLeafCap0Cap0SidePosSideNeg 2817 6446 4507 2518 5988 7154 1632 (-30584) (-3510) 3112 0 0 0 9904)) (.certified (weightedMixedLeafCap0Cap0SidePosSideNeg 2817 4713 4818 5582 1483 3670 1632 4025 (-3510) (-1167) 0 0 0 6781))) (.split (.certified (weightedMixedLeafCap0Cap0SidePosSideNeg 2817 4713 1969 1306 4407 6823 1632 (-4025) (-3510) 1167 0 0 0 14781)) (.certified (weightedMixedLeafCap0Cap0SidePosSideNeg 2817 6446 5040 7757 2095 6518 1632 30584 (-3510) (-3112) 0 0 0 2435))))
          (.split (.split (.certified (weightedMixedLeafCap0Cap0SidePosSideNeg 2817 6886 4750 2851 5565 7753 1632 (-20286) (-3510) 3329 0 0 0 12419)) (.certified (weightedMixedLeafCap0Cap0SidePosSideNeg 2817 5299 5432 5102 1163 3933 1632 4595 (-3510) (-1023) 0 0 7615 0))) (.split (.certified (weightedMixedLeafCap0Cap0SidePosSideNeg 2817 5299 2474 1869 3811 7448 1632 (-4595) (-3510) 1023 0 0 0 10126)) (.certified (weightedMixedLeafCap0Cap0SidePosSideNeg 2817 6886 5630 7419 1882 6670 1632 20286 (-3510) (-3329) 0 0 0 8632))))))
      (.split
        (.split
          (.split
            (.split (.certified (weightedMixedLeafCap0Cap0SidePosSideNeg 3573 6446 5223 7481 6569 9926 2288 (-30584) (-156699) 3112 0 6956 0 9356)) (.split (.split (.certified (weightedMixedLeafCap0Cap0SidePosSideNeg 2942 4713 4767 4961 1159 7474 1712 4025 (-30082) (-1167) 0 0 0 10126)) (.certified (weightedMixedLeafCap0Cap0SidePosSideNeg 4325 4713 6243 4928 1011 8492 2929 4025 82331 (-1167) 0 10220 0 12243))) (.certified (weightedMixedLeafCap0Cap0SidePosSideNeg 3529 4713 5510 4575 1111 7741 2219 4025 (-253273) (-1167) 0 10889 0 9632))))
            (.split (.certified (weightedMixedLeafCap0Cap0SidePosSideNeg 3573 4713 2521 4565 4715 7963 2288 (-4025) (-156699) 1167 0 12092 0 0)) (.split (.certified (weightedMixedLeafCap0Cap0SidePosSideNeg 3624 6446 5873 7825 2198 10038 2365 30584 (-115939) (-3112) 0 8896 0 11970)) (.split (.certified (weightedMixedLeafCap0Cap0SidePosSideNeg 2824 6446 5080 7603 2228 9408 1632 30584 (-32793) (-3112) 0 0 0 5706)) (.split (.certified (weightedMixedLeafCap0Cap0SidePosSideNeg 3470 6446 5553 6925 1459 10074 2077 30584 20873 (-3112) 0 5725 0 6825)) (.certified (weightedMixedLeafCap0Cap0SidePosSideNeg 4924 6446 7123 7933 2489 10134 3476 30584 (-100712) (-3112) 2064 4807 0 10342)))))))
          (.split
            (.split
              (.certified (weightedMixedLeafCap0Cap0SidePosSideNeg 3573 6886 5430 7583 6183 10354 2288 (-20286) (-156699) 3329 0 9676 0 5983))
              (.split
                (.split (.split (.certified (weightedMixedLeafCap0Cap0SidePosSideNeg 2369 5299 4800 4743 1143 8310 1157 4595 (-278519) (-1023) 0 0 9997 1)) (.split (.certified (weightedMixedLeafCap0Cap0SidePosSideNeg 3505 5151 5760 5170 2048 7408 2290 4466 (-16100) (-1063) 0 0 0 6491)) (.split (.certified (weightedMixedLeafCap0Cap0SidePosSideNeg 3505 5249 6178 4420 1299 7158 2290 3910 (-16100) (-600) 0 0 7489 0)) (.certified (weightedMixedLeafCap0Cap0SidePosSideNeg 3505 5733 6056 5895 2048 8153 2290 6015 (-16100) (-1462) 0 0 0 0))))) (.certified (weightedMixedLeafCap0Cap0SidePosSideNeg 4325 5299 6865 5139 1431 9020 2929 4595 82331 (-1023) 0 12077 0 6559)))
                (.split (.certified (weightedMixedLeafCap0Cap0SidePosSideNeg 2824 5299 5389 4676 1034 7727 1632 4595 (-32793) (-1023) 0 0 0 10138)) (.certified (weightedMixedLeafCap0Cap0SidePosSideNeg 4245 5299 6865 4835 1607 8819 2742 4595 55899 (-1023) 0 11527 0 5002)))))
            (.split
              (.certified (weightedMixedLeafCap0Cap0SidePosSideNeg 3573 5299 2926 4730 4160 8490 2288 (-4595) (-156699) 1023 0 11775 0 0))
              (.split
                (.split (.certified (weightedMixedLeafCap0Cap0SidePosSideNeg 2942 6886 5823 7930 2322 10063 1712 20286 (-30082) (-3329) 0 0 8884 1162)) (.split (.certified (weightedMixedLeafCap0Cap0SidePosSideNeg 3598 6886 6352 7435 1769 10830 2239 20286 23814 (-3329) 0 7115 9441 676)) (.split (.certified (weightedMixedLeafCap0Cap0SidePosSideNeg 4959 6774 7648 8293 2977 10660 3699 21882 (-63830) (-3267) 0 8001 0 8575)) (.split (.certified (weightedMixedLeafCap0Cap0SidePosSideNeg 4959 6522 7739 7615 2588 10316 3699 11980 (-63830) (-2709) 0 3746 0 0)) (.certified (weightedMixedLeafCap0Cap0SidePosSideNeg 4959 7521 8212 9069 3773 11431 3699 34349 (-63830) (-4066) 0 7031 6628 1))))))
                (.split
                  (.split (.certified (weightedMixedLeafCap0Cap0SidePosSideNeg 2169 6886 5043 7324 2251 9941 1083 20286 (-1126501) (-3329) 0 0 0 0)) (.certified (weightedMixedLeafCap0Cap0SidePosSideNeg 3455 6886 6290 7798 2145 9539 2200 20286 (-16880) (-3329) 0 0 8908 1022)))
                  (.split
                    (.split (.certified (weightedMixedLeafCap0Cap0SidePosSideNeg 3470 6774 6009 7067 1434 10431 2077 21882 20873 (-3267) 0 7528 0 9106)) (.split (.certified (weightedMixedLeafCap0Cap0SidePosSideNeg 3470 6522 6190 6498 834 10230 2077 11980 20873 (-2709) 1539 6906 0 0)) (.certified (weightedMixedLeafCap0Cap0SidePosSideNeg 3470 7521 6521 7868 2214 11151 2077 34349 20873 (-4066) 377 5807 0 3166))))
                    (.split (.split (.certified (weightedMixedLeafCap0Cap0SidePosSideNeg 4924 6278 7387 7256 2161 9888 3476 12671 (-100712) (-2645) 2247 1522 0 0)) (.certified (weightedMixedLeafCap0Cap0SidePosSideNeg 4924 7310 7822 8717 3359 11005 3476 46509 (-100712) (-3880) 2523 3977 0 7841))) (.split (.certified (weightedMixedLeafCap0Cap0SidePosSideNeg 4924 6522 7695 7312 2397 10107 3476 11980 (-100712) (-2709) 1974 2343 0 0)) (.split (.certified (weightedMixedLeafCap0Cap0SidePosSideNeg 4924 7537 7461 7209 1929 11262 3476 (-40831) (-100712) (-2586) 1466 5277 6176 0)) (.certified (weightedMixedLeafCap0Cap0SidePosSideNeg 4924 7241 8371 9857 4817 10813 3476 13310 (-100712) (-5871) 0 5769 4859 1)))))))))))
        (.split
          (.split
            (.split (.certified (weightedMixedLeafCap0Cap0SidePosSideNeg 5581 6446 7458 5464 7705 9300 5246 (-30584) (-9059) 3112 0 5253 0 8674)) (.certified (weightedMixedLeafCap0Cap0SidePosSideNeg 5581 4713 7083 5593 1525 6357 5246 4025 (-9059) (-1167) 0 10385 0 137)))
            (.split (.certified (weightedMixedLeafCap0Cap0SidePosSideNeg 5581 4713 4783 2984 5159 8096 5246 (-4025) (-9059) 1167 0 6044 0 307)) (.split (.certified (weightedMixedLeafCap0Cap0SidePosSideNeg 5544 6446 7900 8556 3955 9015 5403 30584 (-8841) (-3112) 0 7654 0 9520)) (.split (.certified (weightedMixedLeafCap0Cap0SidePosSideNeg 4916 6446 7230 8004 3172 8219 4034 30584 (-7108) (-3112) 0 0 0 3794)) (.split (.certified (weightedMixedLeafCap0Cap0SidePosSideNeg 5962 6446 8269 8460 3858 9779 5200 30584 (-16703) (-3112) 0 6575 0 9017)) (.certified (weightedMixedLeafCap0Cap0SidePosSideNeg 6628 6446 8999 8646 4939 9236 7374 30584 (-9669) (-3112) 4905 1266 0 8307)))))))
          (.split
            (.split
              (.split
                (.split (.certified (weightedMixedLeafCap0Cap0SidePosSideNeg 4827 6886 6968 5039 6815 9375 4171 (-20286) (-6929) 3329 0 0 0 3642)) (.certified (weightedMixedLeafCap0Cap0SidePosSideNeg 6266 6886 8439 6493 7950 10515 6658 (-20286) (-11263) 3329 0 6888 0 3773)))
                (.split (.certified (weightedMixedLeafCap0Cap0SidePosSideNeg 4916 6886 6947 4987 7035 9167 4034 (-20286) (-7108) 3329 0 0 0 4031)) (.split (.certified (weightedMixedLeafCap0Cap0SidePosSideNeg 5962 6886 7931 6897 7983 10492 5200 (-20286) (-16703) 3329 0 7736 0 6671)) (.split (.certified (weightedMixedLeafCap0Cap0SidePosSideNeg 6628 6774 8754 5944 8269 9994 7374 (-21882) (-9669) 3267 3125 642 0 8112)) (.split (.certified (weightedMixedLeafCap0Cap0SidePosSideNeg 6628 7521 9556 6743 8916 10658 7374 (-34349) (-9669) 4066 4475 1232 0 6154)) (.certified (weightedMixedLeafCap0Cap0SidePosSideNeg 6628 6522 8230 5483 7477 9909 7374 (-11980) (-9669) 2709 3644 926 0 0)))))))
              (.certified (weightedMixedLeafCap0Cap0SidePosSideNeg 5581 5299 7708 5396 2108 6737 5246 4595 (-9059) (-1023) 0 9649 0 1292)))
            (.split
              (.certified (weightedMixedLeafCap0Cap0SidePosSideNeg 5581 5299 5141 3464 4799 8705 5246 (-4595) (-9059) 1023 0 9246 0 3831))
              (.split
                (.split
                  (.certified (weightedMixedLeafCap0Cap0SidePosSideNeg 4827 6886 7734 8118 3553 8625 4171 20286 (-6929) (-3329) 0 0 7290 983))
                  (.split (.split (.certified (weightedMixedLeafCap0Cap0SidePosSideNeg 5923 6774 8683 8718 4264 10188 5543 21882 (-15158) (-3267) 0 7951 0 7603)) (.split (.certified (weightedMixedLeafCap0Cap0SidePosSideNeg 5923 6522 8695 7971 3849 9741 5543 11980 (-15158) (-2709) 0 3836 0 0)) (.certified (weightedMixedLeafCap0Cap0SidePosSideNeg 5923 7521 9294 9447 5060 10982 5543 34349 (-15158) (-4066) 0 7046 5989 0)))) (.split (.certified (weightedMixedLeafCap0Cap0SidePosSideNeg 6534 6774 9322 8811 5246 9539 7942 21882 (-9071) (-3267) 0 7595 0 7058)) (.split (.certified (weightedMixedLeafCap0Cap0SidePosSideNeg 6534 6522 9259 8028 4772 9022 7942 11980 (-9071) (-2709) 0 4265 0 0)) (.certified (weightedMixedLeafCap0Cap0SidePosSideNeg 6534 7521 9976 9487 6047 10341 7942 34349 (-9071) (-4066) 0 6707 5579 1))))))
                (.split
                  (.split (.split (.certified (weightedMixedLeafCap0Cap0SidePosSideNeg 4508 6774 7231 7912 2891 8781 3400 21882 (-8749) (-3267) 0 0 0 6418)) (.certified (weightedMixedLeafCap0Cap0SidePosSideNeg 4508 7001 7523 7856 3017 8932 3400 19014 (-8749) (-3398) 0 0 7877 672))) (.split (.certified (weightedMixedLeafCap0Cap0SidePosSideNeg 5253 6774 8013 7783 3747 8046 4691 21882 (-6011) (-3267) 0 0 0 4776)) (.certified (weightedMixedLeafCap0Cap0SidePosSideNeg 5253 7001 8299 7689 3890 8176 4691 19014 (-6011) (-3398) 0 0 7153 765))))
                  (.split
                    (.split (.split (.certified (weightedMixedLeafCap0Cap0SidePosSideNeg 5962 6278 8443 7696 3526 9415 5200 12671 (-16703) (-2645) 2982 726 0 0)) (.certified (weightedMixedLeafCap0Cap0SidePosSideNeg 5962 7310 9013 9171 4732 10654 5200 46509 (-16703) (-3880) 4076 2312 0 7094))) (.split (.certified (weightedMixedLeafCap0Cap0SidePosSideNeg 5962 6522 8742 7692 3742 9599 5200 11980 (-16703) (-2709) 4478 2460 0 0)) (.split (.certified (weightedMixedLeafCap0Cap0SidePosSideNeg 5962 7537 8744 7712 3308 11075 5200 (-40831) (-16703) (-2586) 0 6583 0 5738)) (.certified (weightedMixedLeafCap0Cap0SidePosSideNeg 5962 7241 9440 10134 6198 10278 5200 13310 (-16703) (-5871) 4324 1937 5238 1)))))
                    (.split
                      (.split (.certified (weightedMixedLeafCap0Cap0SidePosSideNeg 6628 6278 9085 7828 4540 8785 7374 12671 (-9669) (-2645) 2741 1534 0 0)) (.split (.certified (weightedMixedLeafCap0Cap0SidePosSideNeg 6628 7276 9309 7837 4093 10430 7374 (-31130) (-9669) (-2453) 4118 2313 0 6063)) (.certified (weightedMixedLeafCap0Cap0SidePosSideNeg 6628 7080 9864 10204 7182 9532 7374 14934 (-9669) (-5587) 4059 1125 0 5955))))
                      (.split
                        (.certified (weightedMixedLeafCap0Cap0SidePosSideNeg 6628 6522 9373 7776 4728 8941 7374 11980 (-9669) (-2709) 2928 1543 0 0))
                        (.split
                          (.certified (weightedMixedLeafCap0Cap0SidePosSideNeg 6628 7537 9613 7896 4351 10644 7374 (-40831) (-9669) (-2586) 0 7008 0 5050))
                          (.split (.certified (weightedMixedLeafCap0Cap0SidePosSideNeg 6603 7241 10057 10140 7257 9608 7503 13310 (-9506) (-5871) 0 6109 5090 0)) (.split (.certified (weightedMixedLeafCap0Cap0SidePosSideNeg 6307 7241 9773 9772 6863 9214 6570 13310 (-8769) (-5871) 0 0 4859 0)) (.split (.certified (weightedMixedLeafCap0Cap0SidePosSideNeg 6867 7241 10332 10310 7350 10105 7280 13310 (-12357) (-5871) 4549 1134 5110 1)) (.split (.certified (weightedMixedLeafCap0Cap0SidePosSideNeg 7122 7200 10511 10293 7787 9754 8664 13665 (-9939) (-5794) 4336 594 0 5509)) (.split (.certified (weightedMixedLeafCap0Cap0SidePosSideNeg 7122 6975 10358 9892 7460 9426 8664 11256 (-9939) (-5439) 3647 1113 0 0)) (.certified (weightedMixedLeafCap0Cap0SidePosSideNeg 7122 7597 10888 10582 8180 10147 8664 14945 (-9939) (-6460) 4586 700 4818 1)))))))))))))))))))

end Bescovitch
