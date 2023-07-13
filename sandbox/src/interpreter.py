def error():
  raise Exception()

def is_walk(graph, path):
  # initialize visited list with empty list
  visited = ""
  result = True
  while not(path == ""):
      x = path[:1]
      # check if x is part of the graph. if not then abort the loop
      is_in_graph = False
      graph_copy = graph[:]
      while not(graph_copy == []):
          if graph_copy[0][:1] == x:
              is_in_graph = True
              graph_copy = []
          else:
              graph_copy = graph_copy[1:]
      if is_in_graph:
          # check if visited is empty
          if visited == "":
              visited = x
              path = path[1:]
          else:
              # check if x was already visited before
              was_already_visited = False
              visited_copy = visited[:]
              while not(visited_copy == ""):
                  if visited_copy[0] == x:
                      was_already_visited = True
                      visited_copy = ""
                  else:
                      visited_copy = visited_copy[1:]
              if was_already_visited:
                  result = False
                  path = ""
              else:
                  # check if x is reachable from the last visited node (head of visited)
                  is_reachable = False
                  graph_copy = graph[:]
                  while not(graph_copy == []):
                      # find entry for last visited node (head of visited)
                      if graph_copy[0][:1] == visited[:1]:
                          # check if x is in the successors of last visited node (i.e., is reachable)
                          successors = graph_copy[0][1:]
                          while not(successors == ""):
                              if successors[:1] == x:
                                  is_reachable = True
                                  successors = ""
                              else:
                                  successors = successors[1:]
                          graph_copy = []
                      else:
                          graph_copy = graph_copy[1:]
                  if is_reachable:
                      visited = x + visited
                      path = path[1:]
                  else:
                      result = False
                      path = ""
      else:
          error()
  return result

graph = ["abc", "bd", "c", "dac"]
path = "abd"

def factorial(x):
  if x < 0:
    error()
  else:
    y = 1
    while x != 0:
      y = y * x
      x = x - 1
  return y

def match(substr, str):
  while len(str) != 0:
      substr_copy = substr[:]
      str_copy = str[:]
      while len(substr_copy) != 0 and len(str_copy) != 0:
          if substr_copy[:1] == str_copy[:1]:
              substr_copy = substr_copy[1:]
              str_copy = str_copy[1:]
          else:
              str_copy = []
      if len(substr_copy) == 0:
          substr = []
          str = []
      else:
          str = str[1:]
  matched = len(substr) == 0
  return matched

substr = "allo"
str = "aloallo"
