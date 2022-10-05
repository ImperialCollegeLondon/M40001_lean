# Introduction to University Mathematics (M40001/M40009) : additional Lean material

Lean is not an official part of Imperial's Introduction to University Mathematics course, but a lot of the material in Parts I and II is really nice to do in Lean. 

If you are taking the course in October 2022 and you are looking to try doing some of the material in Lean then there are two ways to do it.

## Method 1: try it online

If you have an account at Github then you can
[play the levels online using Gitpod](https://gitpod.io/#https://github.com/ImperialCollegeLondon/M40001_lean). Wait a minute or two for everything to download and set up (basically until all the output at the bottom stops
and the last line says `files extracted: 2718 ...`), then browse your way to `src/2022/logic/sheet1.lean` and try and remove some `sorry`s.

## Method 2: install Lean on your computer.

Instructions on how to install Lean and the supporting tools for doing mathematics in Lean are here on the [Lean 3 installation page](https://leanprover-community.github.io/get_started.html) on the Lean community website. Once you have done this you can just install this M40001/M40009 Lean project by firing up the command line you used to install Lean and typing


```
leanproject get ImperialCollegeLondon/M40001_lean
```

This will install the project on your computer, and then
you can open the `M40001_lean` directory using VS Code
and you should be up and running.

## Getting help if you're stuck (and an Imperial student)

I run a weekly Lean meeting for undergraduates called the Xena Project. It meets on Thursdays 5-8pm in the MLC and on Fridays 5-7pm on the Xena Discord (get access via Imperial student hub).
