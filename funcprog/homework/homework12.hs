
data Month = Jan | Feb | Mar | Apr | May | Jun | Jul | Aug | Sep | Oct | Nov | Dec

type Year = Int

extraDays :: Month -> Int
extraDays Jan = 1
extraDays Mar = 1
extraDays May = 1
extraDays Jul = 1
extraDays Aug = 1
extraDays Oct = 1
extraDays Dec = 1
extraDays _ = 0

leapYear :: Year -> Bool
leapYear year = (mod year 400) == 0 || ((mod year 4) == 0 && not ((mod year 100) == 0))

numberOfDays :: Year -> Month -> Int

numberOfDays year Feb = 28 + if leapYear year then 1 else 0 
numberOfDays _ month = 30 + extraDays month

--numberOfDays _ x | x `elem` [Jan, Mar, May, Jul, Aug, Oct, Dec] = 31

-- test
-- numberOfDays 2017 Jan == 31
-- numberOfDays 2017 Aug == 31
-- numberOfDays 2017 Sep == 30
-- map (numberOfDays 2018) [Jan, Feb, Mar, Apr, May, Jun, Jul, Aug, Sep, Oct, Nov, Dec] == [31, 28, 31, 30, 31, 30, 31, 31, 30, 31, 30, 31]
-- map (numberOfDays 2018) [31,   28,   31, 30,   31,   30, 31, 31,   30, 31,   30, 31]
-- numberOfDays 2016 Feb == 29
-- numberOfDays 1600 Feb == 29
-- numberOfDays 1700 Feb == 28

