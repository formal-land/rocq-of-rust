From Stdlib Require Import List ZArith.
Require Import core.links.result.
Require Import revm.revm_precompile.simulate.interface.
Require Import simulate.RocqOfRust.

Import ListNotations.

Module bls12_381_const.
  Definition G1_ADD_BASE_GAS_FEE : u64 := {| Integer.value := 375 |}.

  Definition G2_ADD_BASE_GAS_FEE : u64 := {| Integer.value := 600 |}.

  Definition G1_MSM_BASE_GAS_FEE : u64 := {| Integer.value := 12000 |}.

  Definition G2_MSM_BASE_GAS_FEE : u64 := {| Integer.value := 22500 |}.

  Definition MAP_FP_TO_G1_BASE_GAS_FEE : u64 := {| Integer.value := 5500 |}.

  Definition MAP_FP2_TO_G2_BASE_GAS_FEE : u64 := {| Integer.value := 23800 |}.

  Definition PAIRING_MULTIPLIER_BASE : u64 := {| Integer.value := 32600 |}.

  Definition PAIRING_OFFSET_BASE : u64 := {| Integer.value := 37700 |}.

  Definition MSM_MULTIPLIER : u64 := {| Integer.value := 1000 |}.

  Definition SCALAR_LENGTH : usize := {| Integer.value := 32 |}.

  Definition FP_LENGTH : usize := {| Integer.value := 48 |}.

  Definition FP_PAD_BY : usize := {| Integer.value := 16 |}.

  Definition PADDED_FP_LENGTH : usize := {| Integer.value := 64 |}.

  Definition PADDED_FP2_LENGTH : usize := {| Integer.value := 128 |}.

  Definition PADDED_G1_LENGTH : usize := {| Integer.value := 128 |}.

  Definition PADDED_G2_LENGTH : usize := {| Integer.value := 256 |}.

  Definition G1_ADD_INPUT_LENGTH : usize := {| Integer.value := 256 |}.

  Definition G2_ADD_INPUT_LENGTH : usize := {| Integer.value := 512 |}.

  Definition G1_MSM_INPUT_LENGTH : usize := {| Integer.value := 160 |}.

  Definition G2_MSM_INPUT_LENGTH : usize := {| Integer.value := 288 |}.

  Definition PAIRING_INPUT_LENGTH : usize := {| Integer.value := 384 |}.

  Definition DISCOUNT_TABLE_G1_MSM : list u16 :=
    [{| Integer.value := 1000 |}; {| Integer.value := 949 |}; {| Integer.value := 848 |}; {| Integer.value := 797 |};
     {| Integer.value := 764 |}; {| Integer.value := 750 |}; {| Integer.value := 738 |}; {| Integer.value := 728 |};
     {| Integer.value := 719 |}; {| Integer.value := 712 |}; {| Integer.value := 705 |}; {| Integer.value := 698 |};
     {| Integer.value := 692 |}; {| Integer.value := 687 |}; {| Integer.value := 682 |}; {| Integer.value := 677 |};
     {| Integer.value := 673 |}; {| Integer.value := 669 |}; {| Integer.value := 665 |}; {| Integer.value := 661 |};
     {| Integer.value := 658 |}; {| Integer.value := 654 |}; {| Integer.value := 651 |}; {| Integer.value := 648 |};
     {| Integer.value := 645 |}; {| Integer.value := 642 |}; {| Integer.value := 640 |}; {| Integer.value := 637 |};
     {| Integer.value := 635 |}; {| Integer.value := 632 |}; {| Integer.value := 630 |}; {| Integer.value := 627 |};
     {| Integer.value := 625 |}; {| Integer.value := 623 |}; {| Integer.value := 621 |}; {| Integer.value := 619 |};
     {| Integer.value := 617 |}; {| Integer.value := 615 |}; {| Integer.value := 613 |}; {| Integer.value := 611 |};
     {| Integer.value := 609 |}; {| Integer.value := 608 |}; {| Integer.value := 606 |}; {| Integer.value := 604 |};
     {| Integer.value := 603 |}; {| Integer.value := 601 |}; {| Integer.value := 599 |}; {| Integer.value := 598 |};
     {| Integer.value := 596 |}; {| Integer.value := 595 |}; {| Integer.value := 593 |}; {| Integer.value := 592 |};
     {| Integer.value := 591 |}; {| Integer.value := 589 |}; {| Integer.value := 588 |}; {| Integer.value := 586 |};
     {| Integer.value := 585 |}; {| Integer.value := 584 |}; {| Integer.value := 582 |}; {| Integer.value := 581 |};
     {| Integer.value := 580 |}; {| Integer.value := 579 |}; {| Integer.value := 577 |}; {| Integer.value := 576 |};
     {| Integer.value := 575 |}; {| Integer.value := 574 |}; {| Integer.value := 573 |}; {| Integer.value := 572 |};
     {| Integer.value := 570 |}; {| Integer.value := 569 |}; {| Integer.value := 568 |}; {| Integer.value := 567 |};
     {| Integer.value := 566 |}; {| Integer.value := 565 |}; {| Integer.value := 564 |}; {| Integer.value := 563 |};
     {| Integer.value := 562 |}; {| Integer.value := 561 |}; {| Integer.value := 560 |}; {| Integer.value := 559 |};
     {| Integer.value := 558 |}; {| Integer.value := 557 |}; {| Integer.value := 556 |}; {| Integer.value := 555 |};
     {| Integer.value := 554 |}; {| Integer.value := 553 |}; {| Integer.value := 552 |}; {| Integer.value := 551 |};
     {| Integer.value := 550 |}; {| Integer.value := 549 |}; {| Integer.value := 548 |}; {| Integer.value := 547 |};
     {| Integer.value := 547 |}; {| Integer.value := 546 |}; {| Integer.value := 545 |}; {| Integer.value := 544 |};
     {| Integer.value := 543 |}; {| Integer.value := 542 |}; {| Integer.value := 541 |}; {| Integer.value := 540 |};
     {| Integer.value := 540 |}; {| Integer.value := 539 |}; {| Integer.value := 538 |}; {| Integer.value := 537 |};
     {| Integer.value := 536 |}; {| Integer.value := 536 |}; {| Integer.value := 535 |}; {| Integer.value := 534 |};
     {| Integer.value := 533 |}; {| Integer.value := 532 |}; {| Integer.value := 532 |}; {| Integer.value := 531 |};
     {| Integer.value := 530 |}; {| Integer.value := 529 |}; {| Integer.value := 528 |}; {| Integer.value := 528 |};
     {| Integer.value := 527 |}; {| Integer.value := 526 |}; {| Integer.value := 525 |}; {| Integer.value := 525 |};
     {| Integer.value := 524 |}; {| Integer.value := 523 |}; {| Integer.value := 522 |}; {| Integer.value := 522 |};
     {| Integer.value := 521 |}; {| Integer.value := 520 |}; {| Integer.value := 520 |}; {| Integer.value := 519 |}].

  Definition DISCOUNT_TABLE_G2_MSM : list u16 :=
    [{| Integer.value := 1000 |}; {| Integer.value := 1000 |}; {| Integer.value := 923 |}; {| Integer.value := 884 |};
     {| Integer.value := 855 |}; {| Integer.value := 832 |}; {| Integer.value := 812 |}; {| Integer.value := 796 |};
     {| Integer.value := 782 |}; {| Integer.value := 770 |}; {| Integer.value := 759 |}; {| Integer.value := 749 |};
     {| Integer.value := 740 |}; {| Integer.value := 732 |}; {| Integer.value := 724 |}; {| Integer.value := 717 |};
     {| Integer.value := 711 |}; {| Integer.value := 704 |}; {| Integer.value := 699 |}; {| Integer.value := 693 |};
     {| Integer.value := 688 |}; {| Integer.value := 683 |}; {| Integer.value := 679 |}; {| Integer.value := 674 |};
     {| Integer.value := 670 |}; {| Integer.value := 666 |}; {| Integer.value := 663 |}; {| Integer.value := 659 |};
     {| Integer.value := 655 |}; {| Integer.value := 652 |}; {| Integer.value := 649 |}; {| Integer.value := 646 |};
     {| Integer.value := 643 |}; {| Integer.value := 640 |}; {| Integer.value := 637 |}; {| Integer.value := 634 |};
     {| Integer.value := 632 |}; {| Integer.value := 629 |}; {| Integer.value := 627 |}; {| Integer.value := 624 |};
     {| Integer.value := 622 |}; {| Integer.value := 620 |}; {| Integer.value := 618 |}; {| Integer.value := 615 |};
     {| Integer.value := 613 |}; {| Integer.value := 611 |}; {| Integer.value := 609 |}; {| Integer.value := 607 |};
     {| Integer.value := 606 |}; {| Integer.value := 604 |}; {| Integer.value := 602 |}; {| Integer.value := 600 |};
     {| Integer.value := 598 |}; {| Integer.value := 597 |}; {| Integer.value := 595 |}; {| Integer.value := 593 |};
     {| Integer.value := 592 |}; {| Integer.value := 590 |}; {| Integer.value := 589 |}; {| Integer.value := 587 |};
     {| Integer.value := 586 |}; {| Integer.value := 584 |}; {| Integer.value := 583 |}; {| Integer.value := 582 |};
     {| Integer.value := 580 |}; {| Integer.value := 579 |}; {| Integer.value := 578 |}; {| Integer.value := 576 |};
     {| Integer.value := 575 |}; {| Integer.value := 574 |}; {| Integer.value := 573 |}; {| Integer.value := 571 |};
     {| Integer.value := 570 |}; {| Integer.value := 569 |}; {| Integer.value := 568 |}; {| Integer.value := 567 |};
     {| Integer.value := 566 |}; {| Integer.value := 565 |}; {| Integer.value := 563 |}; {| Integer.value := 562 |};
     {| Integer.value := 561 |}; {| Integer.value := 560 |}; {| Integer.value := 559 |}; {| Integer.value := 558 |};
     {| Integer.value := 557 |}; {| Integer.value := 556 |}; {| Integer.value := 555 |}; {| Integer.value := 554 |};
     {| Integer.value := 553 |}; {| Integer.value := 552 |}; {| Integer.value := 552 |}; {| Integer.value := 551 |};
     {| Integer.value := 550 |}; {| Integer.value := 549 |}; {| Integer.value := 548 |}; {| Integer.value := 547 |};
     {| Integer.value := 546 |}; {| Integer.value := 545 |}; {| Integer.value := 545 |}; {| Integer.value := 544 |};
     {| Integer.value := 543 |}; {| Integer.value := 542 |}; {| Integer.value := 541 |}; {| Integer.value := 541 |};
     {| Integer.value := 540 |}; {| Integer.value := 539 |}; {| Integer.value := 538 |}; {| Integer.value := 537 |};
     {| Integer.value := 537 |}; {| Integer.value := 536 |}; {| Integer.value := 535 |}; {| Integer.value := 535 |};
     {| Integer.value := 534 |}; {| Integer.value := 533 |}; {| Integer.value := 532 |}; {| Integer.value := 532 |};
     {| Integer.value := 531 |}; {| Integer.value := 530 |}; {| Integer.value := 530 |}; {| Integer.value := 529 |};
     {| Integer.value := 528 |}; {| Integer.value := 528 |}; {| Integer.value := 527 |}; {| Integer.value := 526 |};
     {| Integer.value := 526 |}; {| Integer.value := 525 |}; {| Integer.value := 524 |}; {| Integer.value := 524 |}].
End bls12_381_const.
