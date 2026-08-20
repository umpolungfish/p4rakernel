# Three ob3ects, ready to run

Each ask is one or two lines and names no candidate; the context folder carries
the weight. No provider is named, so the loopback 27B takes it, which is the
default lane for every ob3ect.

```
cd ~/imsgct
C=p4rakernel/p4ramill/Imscribing/Millennium/Erdos/collatz_context

python3 ob3ect/auto.py --desc-file $C/ask_mixing.txt      --name collatz_level_contraction --context $C
python3 ob3ect/auto.py --desc-file $C/ask_open_arm.txt    --name collatz_open_arm          --context $C
python3 ob3ect/auto.py --desc-file $C/ask_two_readings.txt --name collatz_two_readings     --context $C
```

What each is for:

- **collatz_level_contraction** — the mixing rate is measured at 0.81 to 0.87 per
  level and nothing forces it. This asks for the quantity that does.
- **collatz_open_arm** — the repaired words verdict B and stay B, and B is where
  the arm is. This asks what closes it and what the closure costs.
- **collatz_two_readings** — forward leaves density 0.9659^k of classes and banks
  nothing; backward certifies (4/3)^k inside [1, 2^k] and banks everything. This
  asks for the object that holds both and what is conserved across them.

The context folder holds the write-up, the Lean module, every census with the
script that produced it, and the Vox verdict table for all 86 declarations.
