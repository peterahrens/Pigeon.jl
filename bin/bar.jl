using JSON

data = open("foo.json", "r") do f JSON.parse(f) end

println(data)
