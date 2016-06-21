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

/* Add a new vertex to the adjacency list.
 *
 * inputs:
 *
 *   node: The id of the vertex to be added.
 *
 *   g: A pointer to the adjacency list where the vertex will be added.
 *
 * returns:
 *
 *  1: if a new vertex was added.
 *
 *  0: otherwise.
 */
int graph_add_vert(int node, AdjList ** g) {

  AdjList * it = *g;
  AdjList * last = NULL;
  AdjList * new = NULL;

  /* Adjacency list has no vertices. */
  if(*g == NULL){
    new = calloc(1, sizeof(AdjList));
    new->src = node;
    *g = new;
    return 1;
  }

  /* Adjacency list is non-empty. */
  while (it != NULL) {
    /* The current vertex id is less than node. */
    if (it->src < node) {
      last = it;
      it++;
    /* The vertice id already exists in the adjaceny list. */
    } else if (it->src == node) {
      return 0;
    /* it->src is greater than node. */
    } else {
      break;
    }
  }

  new = calloc(1, sizeof(AdjList));
  new->src = node;
  /* There could be only one vertex in the adjacency list in which
     case last would be NULL. */
  if(last == NULL) {
    new->next = *g;
    *g = new;
  /* The last element was less than node and the it->src is greater
     than node or it is empty. Insert new vertex here. */
  } else {
    new->next = last->next;
    last->next = new;
  }
  return 1;

}
