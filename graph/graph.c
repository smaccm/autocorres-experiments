#include <malloc.h>

#define NULL ((void*)0)

typedef struct AdjListNode {
  int dst;
  struct AdjListNode * next;
} AdjListNode;

typedef struct AdjList {
  int src;
  struct AdjListNode * neighbors;
  struct AdjList * next;
} AdjList;

AdjList * graph_empty(void) {
  return NULL;
}

int graph_add_node(int node, AdjList ** g) {

  AdjList * it = *g;
  AdjList * last = NULL;
  AdjList * new = NULL;

  if(it == NULL){
    new = calloc(1, sizeof(AdjList));
    new->src = node;
    *g = new;
    return 1;
  }

  while (it != NULL) {
    if (it->src < node) {
      last = it;
      it++;
    } else if (it->src == node) {
      return 0;
    } else {
      new = calloc(1, sizeof(AdjList));
      new->src = node;
      if(last == NULL) {
        new->next = *g;
        *g = new;
      } else {
        new->next = last->next;
        last->next = new;
      }
      return 1;
    }
  }
}
