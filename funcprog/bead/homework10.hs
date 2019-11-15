type Movie = (String, Double, String)

-- movies :: [(String, Double, String)]
movies :: [Movie]
movies = [ ("Green Book", 8.3, "Peter Farrelly")
         , ("Inception", 8.8, "Christopher Nolan")
         , ("Incredibles 2", 7.7, "Brad Bird")
         , ("The Dark Knight", 9.0, "Christopher Nolan")
         ]



imdbAtLeast :: Double -> Movie -> Bool

imdbAtLeast n (_, score, _) = score >= n

-- test
-- imdbAtLeast 8.8 ("Inception", 8.8, "Christopher Nolan")
-- imdbAtLeast 8.8 ("The Dark Knight", 9.0, "Christopher Nolan")
-- imdbAtLeast 8.3 ("Green Book", 8.3, "Peter Farrelly")
-- not (imdbAtLeast 8.5 ("Green Book", 8.3, "Peter Farrelly"))

director :: String -> Movie -> Bool

director d (_, _, director) = d == director

-- test
-- director "Christopher Nolan" ("Inception", 8.8, "Christopher Nolan")
-- director "Christopher Nolan" ("The Dark Knight", 9.0, "Christopher Nolan")
-- director "Peter Farrelly" ("Green Book", 8.3, "Peter Farrelly")
-- not (director "Peter Farrelly" ("Incredibles 2", 7.7, "Brad Bird"))

and_ :: (Movie -> Bool) -> (Movie -> Bool) -> Movie -> Bool

and_ f1 f2 m = and (map ($ m) [f1, f2])

-- test
-- and_ (director "Brad Bird") (imdbAtLeast 7.5) ("Incredibles 2", 7.7, "Brad Bird")
-- and_ (imdbAtLeast 7.5) (director "Brad Bird")  ("Incredibles 2", 7.7, "Brad Bird")
-- not (and_ (director "Brad Bird") (imdbAtLeast 7.9) ("Incredibles 2", 7.7, "Brad Bird"))
-- not (and_ (director "Christopher Nolan") (imdbAtLeast 7.0) ("Incredibles 2", 7.7, "Brad Bird"))
-- not (and_ (director "Christopher Nolan") (imdbAtLeast 8.0) ("Incredibles 2", 7.7, "Brad Bird"))

or_ :: (Movie -> Bool) -> (Movie -> Bool) -> Movie -> Bool

or_ f1 f2 m = or (map ($ m) [f1, f2])

-- test
-- or_ (director "Christopher Nolan") (imdbAtLeast 8.0) ("Inception", 8.8, "Christopher Nolan")
-- or_ (director "Christopher Nolan") (imdbAtLeast 9.0) ("Inception", 8.8, "Christopher Nolan")
-- or_ (director "Steven Spielberg") (imdbAtLeast 8.2) ("Inception", 8.8, "Christopher Nolan")
-- not (or_ (director "Steven Spielberg") (imdbAtLeast 9.0) ("Green Book", 8.3, "Peter Farrelly"))


search :: (Movie -> Bool) -> [Movie] -> [Movie]

search = filter

-- test
-- search (director "Christopher Nolan") movies == [("Inception", 8.8, "Christopher Nolan"), ("The Dark Knight", 9.0, "Christopher Nolan")]
-- search (imdbAtLeast 8.2) movies == [("Green Book", 8.3, "Peter Farrelly"), ("Inception", 8.8, "Christopher Nolan"), ("The Dark Knight", 9.0, "Christopher Nolan")]
-- search (and_ (director "Christopher Nolan") (imdbAtLeast 8.9)) movies == [("The Dark Knight", 9.0, "Christopher Nolan")]
-- search (or_ (imdbAtLeast 7.5) (director "Rian Johnson")) [("The Last Jedi", 7.2, "Rian Johnson"), ("Sicario", 7.6, "Denis Villeneuve")] == [("The Last Jedi", 7.2, "Rian Johnson"), ("Sicario", 7.6, "Denis Villeneuve")]
-- search (\_ -> True) [] == []
-- search (\_ -> False) movies == []
