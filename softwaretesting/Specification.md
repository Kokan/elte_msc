Square-1 scrambler

## Specification

The aim of this program is to generate a sequence of steps that leaves a solved Square-1[2] after applying those steps in a non-trivially solvable state. The non-trivially solvable state is defined by the WCA[1]. The user could provide the number of steps a sequence must have, and the number of generated sequences. If the user does not provide those values the defaults are 16 steps and 5 sequence.

A Square-1 has three layers, from which the middle layer has two pieces that can be flipped which is called a slice and can be represented with a slash '/'. Each step must end with a slice, this also implies that a slice must be possible. The top and bottom layer has different shaped items, the smallest one is 30° and therefore a smallest move on either of them is 30°, and every other possible move must be a multiple of 30°. A needed movement could be represented with an integer number. The positiv number represents a clockwise, and the negative number represents an anti-clockwise movement. As in one step both the top and bottom pice can be rotated the step must contain two integer number separated with a comma and in the and a slice.

Example: 1, -1 / means rotate top pice with 30° clockwise, and rotate a bottom pice with 30° anti-clockwise and do a slice.

## How to use the program:

Generate with default values (user calls S1 program without any argument):
```
> S1
4,0 / -4,6 / 0,3 / -5,-3 / 0,-4 / 0,6 / -2,1 / 2,-1 / -4,0 / 6,-1 / 1,-2 / -3,4 / -5,2 / 0,4 / 4,6 / 6,-3 /
-2,-4 / 3,-3 / -3,3 / 3,-3 / 0,-3 / 6,3 / -5,6 / 6,-4 / 4,-4 / -4,0 / -4,4 / -5,-4 / 4,6 / 2,2 / 1,-2 / -4,3 /
-5,5 / 3,-3 / 3,-3 / -5,-1 / -3,-3 / 3,6 / -2,6 / -4,-2 / -4,-2 / 4,2 / 2,2 / 0,2 / 2,6 / 0,5 / 0,6 / 2,3 /
6,2 / -3,6 / -3,1 / 0,3 / 1,0 / -4,0 / -2,0 / -5,-4 / 6,2 / 4,-4 / 6,-2 / 2,5 / 6,-3 / 0,-5 / -3,6 / 0,3 /
-5,5 / 0,-3 / 5,-3 / -5,3 / -3,0 / 0,-3 / 1,-1 / 2,-2 / 2,-2 / -4,-4 / -4,0 / -2,-2 / -2,-4 / 6,-2 / 2,-4 / 4,2 /
> 
```

Additionally the user could provide the number of steps as first parameter, and the number of sequences as the second parameter:
```
> S1 5 2
3,-4 / 6,-3 / 6,-3 / 4,-2 / -4,3 /
-5,0 / -4,5 / -2,6 / 0,6 / 6,-3 /
```

[1] https://www.worldcubeassociation.org/regulations/#article-4-scrambling

[2] https://en.wikipedia.org/wiki/Square-1_(puzzle)
