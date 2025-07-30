package roops.core.objects;

//@ model import org.jmlspecs.lang.*;


public class BinomialHeap extends java.lang.Object {

  public /*@ nullable @*/ roops.core.objects.BinomialHeapNode roops_core_objects_BinomialHeap_Nodes;
  public int roops_core_objects_BinomialHeap_size;
  /*@ invariant (\forall roops.core.objects.BinomialHeapNode n; \reach(this.roops_core_objects_BinomialHeap_Nodes, roops.core.objects.BinomialHeapNode, roops_core_objects_BinomialHeapNode_child + roops_core_objects_BinomialHeapNode_sibling).has(((java.lang.Object)(n)))  ==  true; n.roops_core_objects_BinomialHeapNode_parent  !=  null ==> n.roops_core_objects_BinomialHeapNode_key  >=  n.roops_core_objects_BinomialHeapNode_parent.roops_core_objects_BinomialHeapNode_key);
    @*/
  /*@ invariant (\forall roops.core.objects.BinomialHeapNode n; \reach(this.roops_core_objects_BinomialHeap_Nodes, roops.core.objects.BinomialHeapNode, roops_core_objects_BinomialHeapNode_child + roops_core_objects_BinomialHeapNode_sibling).has(((java.lang.Object)(n)))  ==  true; n.roops_core_objects_BinomialHeapNode_sibling  !=  null ==> \reach(n.roops_core_objects_BinomialHeapNode_sibling, roops.core.objects.BinomialHeapNode, roops_core_objects_BinomialHeapNode_child + roops_core_objects_BinomialHeapNode_sibling).has(((java.lang.Object)(n)))  ==  false);
    @*/
  /*@ invariant (\forall roops.core.objects.BinomialHeapNode n; \reach(this.roops_core_objects_BinomialHeap_Nodes, roops.core.objects.BinomialHeapNode, roops_core_objects_BinomialHeapNode_child + roops_core_objects_BinomialHeapNode_sibling).has(((java.lang.Object)(n)))  ==  true; n.roops_core_objects_BinomialHeapNode_child  !=  null ==> \reach(n.roops_core_objects_BinomialHeapNode_child, roops.core.objects.BinomialHeapNode, roops_core_objects_BinomialHeapNode_child + roops_core_objects_BinomialHeapNode_sibling).has(((java.lang.Object)(n)))  ==  false);
    @*/
  /*@ invariant (\forall roops.core.objects.BinomialHeapNode n; \reach(this.roops_core_objects_BinomialHeap_Nodes, roops.core.objects.BinomialHeapNode, roops_core_objects_BinomialHeapNode_child + roops_core_objects_BinomialHeapNode_sibling).has(((java.lang.Object)(n)))  ==  true; (n.roops_core_objects_BinomialHeapNode_child  !=  null && n.roops_core_objects_BinomialHeapNode_sibling  !=  null) ==> (\forall roops.core.objects.BinomialHeapNode m; \reach(n.roops_core_objects_BinomialHeapNode_child, roops.core.objects.BinomialHeapNode, roops_core_objects_BinomialHeapNode_sibling + roops_core_objects_BinomialHeapNode_child).has(((java.lang.Object)(m)))  ==  true; \reach(n.roops_core_objects_BinomialHeapNode_sibling, roops.core.objects.BinomialHeapNode, roops_core_objects_BinomialHeapNode_sibling + roops_core_objects_BinomialHeapNode_child).has(((java.lang.Object)(m)))  ==  false));
    @*/
  /*@ invariant (\forall roops.core.objects.BinomialHeapNode n; \reach(this.roops_core_objects_BinomialHeap_Nodes, roops.core.objects.BinomialHeapNode, roops_core_objects_BinomialHeapNode_child + roops_core_objects_BinomialHeapNode_sibling).has(((java.lang.Object)(n)))  ==  true; (n.roops_core_objects_BinomialHeapNode_child  !=  null && n.roops_core_objects_BinomialHeapNode_sibling  !=  null) ==> (\forall roops.core.objects.BinomialHeapNode m; \reach(n.roops_core_objects_BinomialHeapNode_sibling, roops.core.objects.BinomialHeapNode, roops_core_objects_BinomialHeapNode_sibling + roops_core_objects_BinomialHeapNode_child).has(((java.lang.Object)(m))); \reach(n.roops_core_objects_BinomialHeapNode_child, roops.core.objects.BinomialHeapNode, roops_core_objects_BinomialHeapNode_sibling + roops_core_objects_BinomialHeapNode_child).has(((java.lang.Object)(m)))  ==  false));
    @*/
  /*@ invariant (\forall roops.core.objects.BinomialHeapNode n; \reach(this.roops_core_objects_BinomialHeap_Nodes, roops.core.objects.BinomialHeapNode, roops_core_objects_BinomialHeapNode_child + roops_core_objects_BinomialHeapNode_sibling).has(((java.lang.Object)(n)))  ==  true; n.roops_core_objects_BinomialHeapNode_degree  >=  0);
    @*/
  /*@ invariant (\forall roops.core.objects.BinomialHeapNode n; \reach(this.roops_core_objects_BinomialHeap_Nodes, roops.core.objects.BinomialHeapNode, roops_core_objects_BinomialHeapNode_child + roops_core_objects_BinomialHeapNode_sibling).has(((java.lang.Object)(n)))  ==  true; n.roops_core_objects_BinomialHeapNode_child  ==  null ==> n.roops_core_objects_BinomialHeapNode_degree  ==  0);
    @*/
  /*@ invariant (\forall roops.core.objects.BinomialHeapNode n; \reach(this.roops_core_objects_BinomialHeap_Nodes, roops.core.objects.BinomialHeapNode, roops_core_objects_BinomialHeapNode_child + roops_core_objects_BinomialHeapNode_sibling).has(((java.lang.Object)(n)))  ==  true; n.roops_core_objects_BinomialHeapNode_child  !=  null ==> n.roops_core_objects_BinomialHeapNode_degree  ==  \reach(n.roops_core_objects_BinomialHeapNode_child, roops.core.objects.BinomialHeapNode, roops_core_objects_BinomialHeapNode_sibling).int_size());
    @*/
  /*@ invariant (\forall roops.core.objects.BinomialHeapNode n; \reach(this.roops_core_objects_BinomialHeap_Nodes, roops.core.objects.BinomialHeapNode, roops_core_objects_BinomialHeapNode_child + roops_core_objects_BinomialHeapNode_sibling).has(((java.lang.Object)(n)))  ==  true; n.roops_core_objects_BinomialHeapNode_child  !=  null ==> \reach(n.roops_core_objects_BinomialHeapNode_child.roops_core_objects_BinomialHeapNode_child, roops.core.objects.BinomialHeapNode, roops_core_objects_BinomialHeapNode_sibling + roops_core_objects_BinomialHeapNode_child).int_size()  ==  \reach(n.roops_core_objects_BinomialHeapNode_child.roops_core_objects_BinomialHeapNode_sibling, roops.core.objects.BinomialHeapNode, roops_core_objects_BinomialHeapNode_sibling + roops_core_objects_BinomialHeapNode_child).int_size());
    @*/
  /*@ invariant (\forall roops.core.objects.BinomialHeapNode n; \reach(this.roops_core_objects_BinomialHeap_Nodes, roops.core.objects.BinomialHeapNode, roops_core_objects_BinomialHeapNode_child + roops_core_objects_BinomialHeapNode_sibling).has(((java.lang.Object)(n)))  ==  true; n.roops_core_objects_BinomialHeapNode_child  !=  null ==> (\forall roops.core.objects.BinomialHeapNode m; \reach(n.roops_core_objects_BinomialHeapNode_child, roops.core.objects.BinomialHeapNode, roops_core_objects_BinomialHeapNode_sibling).has(((java.lang.Object)(m)))  ==  true; m.roops_core_objects_BinomialHeapNode_parent  ==  n));
    @*/
  /*@ invariant (\forall roops.core.objects.BinomialHeapNode n; \reach(this.roops_core_objects_BinomialHeap_Nodes, roops.core.objects.BinomialHeapNode, roops_core_objects_BinomialHeapNode_child + roops_core_objects_BinomialHeapNode_sibling).has(((java.lang.Object)(n)))  ==  true; (n.roops_core_objects_BinomialHeapNode_sibling  !=  null && n.roops_core_objects_BinomialHeapNode_parent  !=  null) ==> n.roops_core_objects_BinomialHeapNode_degree  >  n.roops_core_objects_BinomialHeapNode_sibling.roops_core_objects_BinomialHeapNode_degree);
    @*/
  /*@ invariant this.roops_core_objects_BinomialHeap_size  ==  \reach(this.roops_core_objects_BinomialHeap_Nodes, roops.core.objects.BinomialHeapNode, roops_core_objects_BinomialHeapNode_child + roops_core_objects_BinomialHeapNode_sibling).int_size();
    @*/
  /*@ invariant (\forall roops.core.objects.BinomialHeapNode n; \reach(this.roops_core_objects_BinomialHeap_Nodes, roops.core.objects.BinomialHeapNode, roops_core_objects_BinomialHeapNode_sibling).has(((java.lang.Object)(n)))  ==  true; (n.roops_core_objects_BinomialHeapNode_sibling  !=  null ==> n.roops_core_objects_BinomialHeapNode_degree  <  n.roops_core_objects_BinomialHeapNode_sibling.roops_core_objects_BinomialHeapNode_degree) && (n.roops_core_objects_BinomialHeapNode_parent  ==  null));
    @*/
  /*@ invariant (\forall roops.core.objects.BinomialHeapNode n; \reach(this.roops_core_objects_BinomialHeap_Nodes, roops.core.objects.BinomialHeapNode, roops_core_objects_BinomialHeapNode_sibling).has(((java.lang.Object)(n)))  ==  true; n.roops_core_objects_BinomialHeapNode_key  >=  0);
    @*/

  public BinomialHeap() {
    this.roops_core_objects_BinomialHeap_Nodes = ((roops.core.objects.BinomialHeapNode)(null));
    this.roops_core_objects_BinomialHeap_size = (byte)0;
    {
    }
  }


  /*@ 
    @ requires true;
    @ ensures (\forall roops.core.objects.BinomialHeapNode n; \old(\reach(this.roops_core_objects_BinomialHeap_Nodes, roops.core.objects.BinomialHeapNode, roops_core_objects_BinomialHeapNode_sibling + roops_core_objects_BinomialHeapNode_child)).has(((java.lang.Object)(n)))  ==  true; \reach(this.roops_core_objects_BinomialHeap_Nodes, roops.core.objects.BinomialHeapNode, roops_core_objects_BinomialHeapNode_sibling + roops_core_objects_BinomialHeapNode_child).has(((java.lang.Object)(n)))  ==  true && \old(n.roops_core_objects_BinomialHeapNode_key)  ==  n.roops_core_objects_BinomialHeapNode_key);
    @ ensures value  >  0 ==> (\exists roops.core.objects.BinomialHeapNode n; \old(\reach(this.roops_core_objects_BinomialHeap_Nodes, roops.core.objects.BinomialHeapNode, roops_core_objects_BinomialHeapNode_sibling + roops_core_objects_BinomialHeapNode_child)).has(((java.lang.Object)(n)))  ==  false; \reach(this.roops_core_objects_BinomialHeap_Nodes, roops.core.objects.BinomialHeapNode, roops_core_objects_BinomialHeapNode_sibling + roops_core_objects_BinomialHeapNode_child).has(((java.lang.Object)(n))) && n.roops_core_objects_BinomialHeapNode_key  ==  value);
    @ ensures value  >  0 ==> this.roops_core_objects_BinomialHeap_size  ==  \old(this.roops_core_objects_BinomialHeap_size) + 1;
    @ signals (java.lang.Exception e) false;
    @*/
  public void insert(int value) {
    int param_value_21;

    param_value_21 = value;
    {
      boolean t_643;

      t_643 = param_value_21  >  0;
      if (t_643) {
        {
          {
            {
              {
                {
                  roops.core.objects.BinomialHeapNode t_640;
                  boolean t_642;

                  t_640 = new roops.core.objects.BinomialHeapNode();
                  roops.core.objects.BinomialHeapNode var_115_temp = t_640;

                  var_115_temp.roops_core_objects_BinomialHeapNode_key = param_value_21;
                  t_642 = this.roops_core_objects_BinomialHeap_Nodes  ==  null;
                  if (t_642) {
                    {
                      {
                        {
                          {
                            {
                              this.roops_core_objects_BinomialHeap_Nodes = var_115_temp;
                              this.roops_core_objects_BinomialHeap_size = 1;
                            }
                          }
                        }
                      }
                    }
                  } else {
                    {
                      {
                        {
                          {
                            {
                              int t_641;

                              this.unionNodes(var_115_temp);
                              t_641 = this.roops_core_objects_BinomialHeap_size;
                              this.roops_core_objects_BinomialHeap_size = this.roops_core_objects_BinomialHeap_size + (byte)1;
                            }
                          }
                        }
                      }
                    }
                  }
                }
              }
            }
          }
        }
      }
    }
  }


  private static roops.core.objects.BinomialHeapNode findMinNode(roops.core.objects.BinomialHeapNode arg) {
    {
      roops.core.objects.BinomialHeapNode param_arg_22;

      param_arg_22 = arg;
      {
        roops.core.objects.BinomialHeapNode var_116_x = param_arg_22, var_117_y = param_arg_22;
        int var_118_min = var_116_x.roops_core_objects_BinomialHeapNode_key;

        {
          {
            boolean t_651;
            boolean t_652;
            boolean t_653;

            t_651 = var_116_x  !=  null;

            if (t_651) {
              {
                {
                  {
                    {
                      {
                        boolean t_650;

                        {
                          boolean t_644;

                          t_644 = var_116_x.roops_core_objects_BinomialHeapNode_key  <  var_118_min;

                          if (t_644) {
                            {
                              {
                                {
                                  {
                                    {
                                      var_117_y = var_116_x;
                                      var_118_min = var_116_x.roops_core_objects_BinomialHeapNode_key;
                                    }
                                  }
                                }
                              }
                            }
                          }
                          var_116_x = var_116_x.roops_core_objects_BinomialHeapNode_sibling;
                        }
                        t_650 = var_116_x  !=  null;
                        if (t_650) {
                          {
                            {
                              {
                                {
                                  {
                                    boolean t_649;

                                    {
                                      boolean t_645;

                                      t_645 = var_116_x.roops_core_objects_BinomialHeapNode_key  <  var_118_min;

                                      if (t_645) {
                                        {
                                          {
                                            {
                                              {
                                                {
                                                  var_117_y = var_116_x;
                                                  var_118_min = var_116_x.roops_core_objects_BinomialHeapNode_key;
                                                }
                                              }
                                            }
                                          }
                                        }
                                      }
                                      var_116_x = var_116_x.roops_core_objects_BinomialHeapNode_sibling;
                                    }
                                    t_649 = var_116_x  !=  null;
                                    if (t_649) {
                                      {
                                        {
                                          {
                                            {
                                              {
                                                boolean t_648;

                                                {
                                                  boolean t_646;

                                                  t_646 = var_116_x.roops_core_objects_BinomialHeapNode_key  <  var_118_min;

                                                  if (t_646) {
                                                    {
                                                      {
                                                        {
                                                          {
                                                            {
                                                              var_117_y = var_116_x;
                                                              var_118_min = var_116_x.roops_core_objects_BinomialHeapNode_key;
                                                            }
                                                          }
                                                        }
                                                      }
                                                    }
                                                  }
                                                  var_116_x = var_116_x.roops_core_objects_BinomialHeapNode_sibling;
                                                }
                                                t_648 = var_116_x  !=  null;
                                                if (t_648) {
                                                  {
                                                    {
                                                      {
                                                        {
                                                          {
                                                            boolean t_647;

                                                            t_647 = var_116_x.roops_core_objects_BinomialHeapNode_key  <  var_118_min;

                                                            if (t_647) {
                                                              {
                                                                {
                                                                  {
                                                                    {
                                                                      {
                                                                        var_117_y = var_116_x;
                                                                        var_118_min = var_116_x.roops_core_objects_BinomialHeapNode_key;
                                                                      }
                                                                    }
                                                                  }
                                                                }
                                                              }
                                                            }
                                                            var_116_x = var_116_x.roops_core_objects_BinomialHeapNode_sibling;
                                                          }
                                                        }
                                                      }
                                                    }
                                                  }
                                                }
                                              }
                                            }
                                          }
                                        }
                                      }
                                    }
                                  }
                                }
                              }
                            }
                          }
                        }
                      }
                    }
                  }
                }
              }
            }
            t_652 = var_116_x  !=  null;
            t_653 = ! t_652;
            assert t_653;
          }
        }
        if (true) return var_117_y;
      }
    }

    return null;
  }


  /*@ 
    @ requires true;
    @ ensures true;
    @*/
  public void generateInvariant() {
    {
      {
        this.roops_core_objects_BinomialHeap_Nodes = this.roops_core_objects_BinomialHeap_Nodes;
      }
    }
  }


  /*@ 
    @ requires true;
    @ ensures \old(this.roops_core_objects_BinomialHeap_Nodes)  !=  null ==> \old(\reach(this.roops_core_objects_BinomialHeap_Nodes, roops.core.objects.BinomialHeapNode, roops_core_objects_BinomialHeapNode_sibling + roops_core_objects_BinomialHeapNode_child)).has(((java.lang.Object)(\result)))  ==  true;
    @ ensures (\forall roops.core.objects.BinomialHeapNode n; \reach(this.roops_core_objects_BinomialHeap_Nodes, roops.core.objects.BinomialHeapNode, roops_core_objects_BinomialHeapNode_sibling + roops_core_objects_BinomialHeapNode_child).has(((java.lang.Object)(n)))  ==  true; \result.roops_core_objects_BinomialHeapNode_key  <=  n.roops_core_objects_BinomialHeapNode_key);
    @ ensures (\forall roops.core.objects.BinomialHeapNode n; \reach(this.roops_core_objects_BinomialHeap_Nodes, roops.core.objects.BinomialHeapNode, roops_core_objects_BinomialHeapNode_sibling + roops_core_objects_BinomialHeapNode_child).has(((java.lang.Object)(n)))  ==  true; \old(n.roops_core_objects_BinomialHeapNode_key)  ==  n.roops_core_objects_BinomialHeapNode_key);
    @ signals (java.lang.Exception e) false;
    @*/
  public roops.core.objects.BinomialHeapNode extractMin() {
    {
      {
        boolean t_654;
        roops.core.objects.BinomialHeapNode t_655;
        boolean t_662;
        boolean t_680;
        boolean t_681;
        boolean t_682;

        t_654 = this.roops_core_objects_BinomialHeap_Nodes  ==  null;

        if (t_654) {
          {
            {
              {
                {
                  {
                    if (true) return ((roops.core.objects.BinomialHeapNode)(null));
                  }
                }
              }
            }
          }
        }
        roops.core.objects.BinomialHeapNode var_119_temp = this.roops_core_objects_BinomialHeap_Nodes, var_120_prevTemp = ((roops.core.objects.BinomialHeapNode)(null));

        t_655 = findMinNode(this.roops_core_objects_BinomialHeap_Nodes);
        roops.core.objects.BinomialHeapNode var_121_minNode = t_655;

        {
          {
            boolean t_659;
            boolean t_660;
            boolean t_661;

            t_659 = var_119_temp.roops_core_objects_BinomialHeapNode_key  !=  var_121_minNode.roops_core_objects_BinomialHeapNode_key;

            if (t_659) {
              {
                {
                  {
                    {
                      {
                        boolean t_658;

                        {
                          var_120_prevTemp = var_119_temp;
                          var_119_temp = var_119_temp.roops_core_objects_BinomialHeapNode_sibling;
                        }
                        t_658 = var_119_temp.roops_core_objects_BinomialHeapNode_key  !=  var_121_minNode.roops_core_objects_BinomialHeapNode_key;
                        if (t_658) {
                          {
                            {
                              {
                                {
                                  {
                                    boolean t_657;

                                    {
                                      var_120_prevTemp = var_119_temp;
                                      var_119_temp = var_119_temp.roops_core_objects_BinomialHeapNode_sibling;
                                    }
                                    t_657 = var_119_temp.roops_core_objects_BinomialHeapNode_key  !=  var_121_minNode.roops_core_objects_BinomialHeapNode_key;
                                    if (t_657) {
                                      {
                                        {
                                          {
                                            {
                                              {
                                                boolean t_656;

                                                {
                                                  var_120_prevTemp = var_119_temp;
                                                  var_119_temp = var_119_temp.roops_core_objects_BinomialHeapNode_sibling;
                                                }
                                                t_656 = var_119_temp.roops_core_objects_BinomialHeapNode_key  !=  var_121_minNode.roops_core_objects_BinomialHeapNode_key;
                                                if (t_656) {
                                                  {
                                                    {
                                                      {
                                                        {
                                                          {
                                                            var_120_prevTemp = var_119_temp;
                                                            var_119_temp = var_119_temp.roops_core_objects_BinomialHeapNode_sibling;
                                                          }
                                                        }
                                                      }
                                                    }
                                                  }
                                                }
                                              }
                                            }
                                          }
                                        }
                                      }
                                    }
                                  }
                                }
                              }
                            }
                          }
                        }
                      }
                    }
                  }
                }
              }
            }
            t_660 = var_119_temp.roops_core_objects_BinomialHeapNode_key  !=  var_121_minNode.roops_core_objects_BinomialHeapNode_key;
            t_661 = ! t_660;
            assert t_661;
          }
        }
        t_662 = var_120_prevTemp  ==  null;

        if (t_662) {
          {
            {
              {
                {
                  {
                    this.roops_core_objects_BinomialHeap_Nodes = var_119_temp.roops_core_objects_BinomialHeapNode_sibling;
                  }
                }
              }
            }
          }
        } else {
          {
            {
              {
                {
                  {
                    var_120_prevTemp.roops_core_objects_BinomialHeapNode_sibling = var_119_temp.roops_core_objects_BinomialHeapNode_sibling;
                  }
                }
              }
            }
          }
        }
        var_119_temp = var_119_temp.roops_core_objects_BinomialHeapNode_child;
        roops.core.objects.BinomialHeapNode var_122_fakeNode = var_119_temp;

        {
          {
            boolean t_666;
            boolean t_667;
            boolean t_668;

            t_666 = var_119_temp  !=  null;

            if (t_666) {
              {
                {
                  {
                    {
                      {
                        boolean t_665;

                        {
                          var_119_temp.roops_core_objects_BinomialHeapNode_parent = ((roops.core.objects.BinomialHeapNode)(null));
                          var_119_temp = var_119_temp.roops_core_objects_BinomialHeapNode_sibling;
                        }
                        t_665 = var_119_temp  !=  null;
                        if (t_665) {
                          {
                            {
                              {
                                {
                                  {
                                    boolean t_664;

                                    {
                                      var_119_temp.roops_core_objects_BinomialHeapNode_parent = ((roops.core.objects.BinomialHeapNode)(null));
                                      var_119_temp = var_119_temp.roops_core_objects_BinomialHeapNode_sibling;
                                    }
                                    t_664 = var_119_temp  !=  null;
                                    if (t_664) {
                                      {
                                        {
                                          {
                                            {
                                              {
                                                boolean t_663;

                                                {
                                                  var_119_temp.roops_core_objects_BinomialHeapNode_parent = ((roops.core.objects.BinomialHeapNode)(null));
                                                  var_119_temp = var_119_temp.roops_core_objects_BinomialHeapNode_sibling;
                                                }
                                                t_663 = var_119_temp  !=  null;
                                                if (t_663) {
                                                  {
                                                    {
                                                      {
                                                        {
                                                          {
                                                            var_119_temp.roops_core_objects_BinomialHeapNode_parent = ((roops.core.objects.BinomialHeapNode)(null));
                                                            var_119_temp = var_119_temp.roops_core_objects_BinomialHeapNode_sibling;
                                                          }
                                                        }
                                                      }
                                                    }
                                                  }
                                                }
                                              }
                                            }
                                          }
                                        }
                                      }
                                    }
                                  }
                                }
                              }
                            }
                          }
                        }
                      }
                    }
                  }
                }
              }
            }
            t_667 = var_119_temp  !=  null;
            t_668 = ! t_667;
            assert t_668;
          }
        }
        {
          t_681 = this.roops_core_objects_BinomialHeap_Nodes  ==  null;
          if (t_681) {
            {
              {
                t_682 = var_122_fakeNode  ==  null;
                if (t_682) {
                  {
                    t_680 = true;
                  }
                } else {
                  {
                    t_680 = false;
                  }
                }
              }
            }
          } else {
            {
              t_680 = false;
            }
          }
        }

        if (t_680) {
          {
            {
              {
                {
                  {
                    this.roops_core_objects_BinomialHeap_size = 0;
                  }
                }
              }
            }
          }
        } else {
          {
            {
              {
                {
                  {
                    boolean t_677;
                    boolean t_678;
                    boolean t_679;

                    {
                      t_678 = this.roops_core_objects_BinomialHeap_Nodes  ==  null;
                      if (t_678) {
                        {
                          {
                            t_679 = var_122_fakeNode  !=  null;
                            if (t_679) {
                              {
                                t_677 = true;
                              }
                            } else {
                              {
                                t_677 = false;
                              }
                            }
                          }
                        }
                      } else {
                        {
                          t_677 = false;
                        }
                      }
                    }
                    if (t_677) {
                      {
                        {
                          {
                            {
                              {
                                roops.core.objects.BinomialHeapNode t_669;
                                int t_670;

                                t_669 = var_122_fakeNode.reverse(((roops.core.objects.BinomialHeapNode)(null)));
                                this.roops_core_objects_BinomialHeap_Nodes = t_669;
                                t_670 = this.roops_core_objects_BinomialHeap_size;
                                this.roops_core_objects_BinomialHeap_size = this.roops_core_objects_BinomialHeap_size + (byte)-1;
                              }
                            }
                          }
                        }
                      }
                    } else {
                      {
                        {
                          {
                            {
                              {
                                boolean t_674;
                                boolean t_675;
                                boolean t_676;

                                {
                                  t_675 = this.roops_core_objects_BinomialHeap_Nodes  !=  null;
                                  if (t_675) {
                                    {
                                      {
                                        t_676 = var_122_fakeNode  ==  null;
                                        if (t_676) {
                                          {
                                            t_674 = true;
                                          }
                                        } else {
                                          {
                                            t_674 = false;
                                          }
                                        }
                                      }
                                    }
                                  } else {
                                    {
                                      t_674 = false;
                                    }
                                  }
                                }
                                if (t_674) {
                                  {
                                    {
                                      {
                                        {
                                          {
                                            int t_671;

                                            t_671 = this.roops_core_objects_BinomialHeap_size;
                                            this.roops_core_objects_BinomialHeap_size = this.roops_core_objects_BinomialHeap_size + (byte)-1;
                                          }
                                        }
                                      }
                                    }
                                  }
                                } else {
                                  {
                                    {
                                      {
                                        {
                                          {
                                            roops.core.objects.BinomialHeapNode t_672;
                                            int t_673;

                                            t_672 = var_122_fakeNode.reverse(((roops.core.objects.BinomialHeapNode)(null)));
                                            this.unionNodes(t_672);
                                            t_673 = this.roops_core_objects_BinomialHeap_size;
                                            this.roops_core_objects_BinomialHeap_size = this.roops_core_objects_BinomialHeap_size + (byte)-1;
                                          }
                                        }
                                      }
                                    }
                                  }
                                }
                              }
                            }
                          }
                        }
                      }
                    }
                  }
                }
              }
            }
          }
        }
        if (true) return var_121_minNode;
      }
    }

    return null;
  }


  private void merge(roops.core.objects.BinomialHeapNode binHeap) {
    roops.core.objects.BinomialHeapNode param_binHeap_23;

    param_binHeap_23 = binHeap;
    {
      boolean t_729;
      roops.core.objects.BinomialHeapNode var_123_temp1 = this.roops_core_objects_BinomialHeap_Nodes, var_124_temp2 = param_binHeap_23;

      {
        {
          boolean t_716;
          boolean t_717;
          boolean t_718;
          boolean t_719;
          boolean t_720;
          boolean t_721;
          boolean t_722;

          {
            t_717 = var_123_temp1  !=  null;
            if (t_717) {
              {
                {
                  t_718 = var_124_temp2  !=  null;
                  if (t_718) {
                    {
                      t_716 = true;
                    }
                  } else {
                    {
                      t_716 = false;
                    }
                  }
                }
              }
            } else {
              {
                t_716 = false;
              }
            }
          }

          if (t_716) {
            {
              {
                {
                  {
                    {
                      boolean t_713;
                      boolean t_714;
                      boolean t_715;

                      {
                        boolean t_688;

                        t_688 = var_123_temp1.roops_core_objects_BinomialHeapNode_degree  ==  var_124_temp2.roops_core_objects_BinomialHeapNode_degree;
                        if (t_688) {
                          {
                            {
                              {
                                {
                                  {
                                    roops.core.objects.BinomialHeapNode var_125_tmp_4_4 = var_124_temp2;

                                    var_124_temp2 = var_124_temp2.roops_core_objects_BinomialHeapNode_sibling;
                                    var_125_tmp_4_4.roops_core_objects_BinomialHeapNode_sibling = var_123_temp1.roops_core_objects_BinomialHeapNode_sibling;
                                    var_123_temp1.roops_core_objects_BinomialHeapNode_sibling = var_125_tmp_4_4;
                                    var_123_temp1 = var_125_tmp_4_4.roops_core_objects_BinomialHeapNode_sibling;
                                  }
                                }
                              }
                            }
                          }
                        } else {
                          {
                            {
                              {
                                {
                                  {
                                    boolean t_687;

                                    t_687 = var_123_temp1.roops_core_objects_BinomialHeapNode_degree  <  var_124_temp2.roops_core_objects_BinomialHeapNode_degree;
                                    if (t_687) {
                                      {
                                        {
                                          {
                                            {
                                              {
                                                boolean t_683;
                                                boolean t_684;
                                                boolean t_685;

                                                {
                                                  t_684 = var_123_temp1.roops_core_objects_BinomialHeapNode_sibling  ==  null;
                                                  if (t_684) {
                                                    {
                                                      t_683 = true;
                                                    }
                                                  } else {
                                                    {
                                                      {
                                                        t_685 = var_123_temp1.roops_core_objects_BinomialHeapNode_sibling.roops_core_objects_BinomialHeapNode_degree  >  var_124_temp2.roops_core_objects_BinomialHeapNode_degree;
                                                        if (t_685) {
                                                          {
                                                            t_683 = true;
                                                          }
                                                        } else {
                                                          {
                                                            t_683 = false;
                                                          }
                                                        }
                                                      }
                                                    }
                                                  }
                                                }
                                                if (t_683) {
                                                  {
                                                    {
                                                      {
                                                        {
                                                          {
                                                            roops.core.objects.BinomialHeapNode var_126_tmp_4_4 = var_124_temp2;

                                                            var_124_temp2 = var_124_temp2.roops_core_objects_BinomialHeapNode_sibling;
                                                            var_126_tmp_4_4.roops_core_objects_BinomialHeapNode_sibling = var_123_temp1.roops_core_objects_BinomialHeapNode_sibling;
                                                            var_123_temp1.roops_core_objects_BinomialHeapNode_sibling = var_126_tmp_4_4;
                                                            var_123_temp1 = var_126_tmp_4_4.roops_core_objects_BinomialHeapNode_sibling;
                                                          }
                                                        }
                                                      }
                                                    }
                                                  }
                                                } else {
                                                  {
                                                    {
                                                      {
                                                        {
                                                          {
                                                            var_123_temp1 = var_123_temp1.roops_core_objects_BinomialHeapNode_sibling;
                                                          }
                                                        }
                                                      }
                                                    }
                                                  }
                                                }
                                              }
                                            }
                                          }
                                        }
                                      }
                                    } else {
                                      {
                                        {
                                          {
                                            {
                                              {
                                                boolean t_686;
                                                roops.core.objects.BinomialHeapNode var_127_tmp_4_4 = var_123_temp1;

                                                var_123_temp1 = var_124_temp2;
                                                var_124_temp2 = var_124_temp2.roops_core_objects_BinomialHeapNode_sibling;
                                                var_123_temp1.roops_core_objects_BinomialHeapNode_sibling = var_127_tmp_4_4;
                                                t_686 = var_127_tmp_4_4  ==  this.roops_core_objects_BinomialHeap_Nodes;
                                                if (t_686) {
                                                  {
                                                    {
                                                      {
                                                        {
                                                          {
                                                            this.roops_core_objects_BinomialHeap_Nodes = var_123_temp1;
                                                          }
                                                        }
                                                      }
                                                    }
                                                  }
                                                }
                                              }
                                            }
                                          }
                                        }
                                      }
                                    }
                                  }
                                }
                              }
                            }
                          }
                        }
                      }
                      {
                        t_714 = var_123_temp1  !=  null;
                        if (t_714) {
                          {
                            {
                              t_715 = var_124_temp2  !=  null;
                              if (t_715) {
                                {
                                  t_713 = true;
                                }
                              } else {
                                {
                                  t_713 = false;
                                }
                              }
                            }
                          }
                        } else {
                          {
                            t_713 = false;
                          }
                        }
                      }
                      if (t_713) {
                        {
                          {
                            {
                              {
                                {
                                  boolean t_710;
                                  boolean t_711;
                                  boolean t_712;

                                  {
                                    boolean t_694;

                                    t_694 = var_123_temp1.roops_core_objects_BinomialHeapNode_degree  ==  var_124_temp2.roops_core_objects_BinomialHeapNode_degree;
                                    if (t_694) {
                                      {
                                        {
                                          {
                                            {
                                              {
                                                roops.core.objects.BinomialHeapNode var_128_tmp_4_3 = var_124_temp2;

                                                var_124_temp2 = var_124_temp2.roops_core_objects_BinomialHeapNode_sibling;
                                                var_128_tmp_4_3.roops_core_objects_BinomialHeapNode_sibling = var_123_temp1.roops_core_objects_BinomialHeapNode_sibling;
                                                var_123_temp1.roops_core_objects_BinomialHeapNode_sibling = var_128_tmp_4_3;
                                                var_123_temp1 = var_128_tmp_4_3.roops_core_objects_BinomialHeapNode_sibling;
                                              }
                                            }
                                          }
                                        }
                                      }
                                    } else {
                                      {
                                        {
                                          {
                                            {
                                              {
                                                boolean t_693;

                                                t_693 = var_123_temp1.roops_core_objects_BinomialHeapNode_degree  <  var_124_temp2.roops_core_objects_BinomialHeapNode_degree;
                                                if (t_693) {
                                                  {
                                                    {
                                                      {
                                                        {
                                                          {
                                                            boolean t_689;
                                                            boolean t_690;
                                                            boolean t_691;

                                                            {
                                                              t_690 = var_123_temp1.roops_core_objects_BinomialHeapNode_sibling  ==  null;
                                                              if (t_690) {
                                                                {
                                                                  t_689 = true;
                                                                }
                                                              } else {
                                                                {
                                                                  {
                                                                    t_691 = var_123_temp1.roops_core_objects_BinomialHeapNode_sibling.roops_core_objects_BinomialHeapNode_degree  >  var_124_temp2.roops_core_objects_BinomialHeapNode_degree;
                                                                    if (t_691) {
                                                                      {
                                                                        t_689 = true;
                                                                      }
                                                                    } else {
                                                                      {
                                                                        t_689 = false;
                                                                      }
                                                                    }
                                                                  }
                                                                }
                                                              }
                                                            }
                                                            if (t_689) {
                                                              {
                                                                {
                                                                  {
                                                                    {
                                                                      {
                                                                        roops.core.objects.BinomialHeapNode var_129_tmp_4_3 = var_124_temp2;

                                                                        var_124_temp2 = var_124_temp2.roops_core_objects_BinomialHeapNode_sibling;
                                                                        var_129_tmp_4_3.roops_core_objects_BinomialHeapNode_sibling = var_123_temp1.roops_core_objects_BinomialHeapNode_sibling;
                                                                        var_123_temp1.roops_core_objects_BinomialHeapNode_sibling = var_129_tmp_4_3;
                                                                        var_123_temp1 = var_129_tmp_4_3.roops_core_objects_BinomialHeapNode_sibling;
                                                                      }
                                                                    }
                                                                  }
                                                                }
                                                              }
                                                            } else {
                                                              {
                                                                {
                                                                  {
                                                                    {
                                                                      {
                                                                        var_123_temp1 = var_123_temp1.roops_core_objects_BinomialHeapNode_sibling;
                                                                      }
                                                                    }
                                                                  }
                                                                }
                                                              }
                                                            }
                                                          }
                                                        }
                                                      }
                                                    }
                                                  }
                                                } else {
                                                  {
                                                    {
                                                      {
                                                        {
                                                          {
                                                            boolean t_692;
                                                            roops.core.objects.BinomialHeapNode var_130_tmp_4_3 = var_123_temp1;

                                                            var_123_temp1 = var_124_temp2;
                                                            var_124_temp2 = var_124_temp2.roops_core_objects_BinomialHeapNode_sibling;
                                                            var_123_temp1.roops_core_objects_BinomialHeapNode_sibling = var_130_tmp_4_3;
                                                            t_692 = var_130_tmp_4_3  ==  this.roops_core_objects_BinomialHeap_Nodes;
                                                            if (t_692) {
                                                              {
                                                                {
                                                                  {
                                                                    {
                                                                      {
                                                                        this.roops_core_objects_BinomialHeap_Nodes = var_123_temp1;
                                                                      }
                                                                    }
                                                                  }
                                                                }
                                                              }
                                                            }
                                                          }
                                                        }
                                                      }
                                                    }
                                                  }
                                                }
                                              }
                                            }
                                          }
                                        }
                                      }
                                    }
                                  }
                                  {
                                    t_711 = var_123_temp1  !=  null;
                                    if (t_711) {
                                      {
                                        {
                                          t_712 = var_124_temp2  !=  null;
                                          if (t_712) {
                                            {
                                              t_710 = true;
                                            }
                                          } else {
                                            {
                                              t_710 = false;
                                            }
                                          }
                                        }
                                      }
                                    } else {
                                      {
                                        t_710 = false;
                                      }
                                    }
                                  }
                                  if (t_710) {
                                    {
                                      {
                                        {
                                          {
                                            {
                                              boolean t_707;
                                              boolean t_708;
                                              boolean t_709;

                                              {
                                                boolean t_700;

                                                t_700 = var_123_temp1.roops_core_objects_BinomialHeapNode_degree  ==  var_124_temp2.roops_core_objects_BinomialHeapNode_degree;
                                                if (t_700) {
                                                  {
                                                    {
                                                      {
                                                        {
                                                          {
                                                            roops.core.objects.BinomialHeapNode var_131_tmp_4_2 = var_124_temp2;

                                                            var_124_temp2 = var_124_temp2.roops_core_objects_BinomialHeapNode_sibling;
                                                            var_131_tmp_4_2.roops_core_objects_BinomialHeapNode_sibling = var_123_temp1.roops_core_objects_BinomialHeapNode_sibling;
                                                            var_123_temp1.roops_core_objects_BinomialHeapNode_sibling = var_131_tmp_4_2;
                                                            var_123_temp1 = var_131_tmp_4_2.roops_core_objects_BinomialHeapNode_sibling;
                                                          }
                                                        }
                                                      }
                                                    }
                                                  }
                                                } else {
                                                  {
                                                    {
                                                      {
                                                        {
                                                          {
                                                            boolean t_699;

                                                            t_699 = var_123_temp1.roops_core_objects_BinomialHeapNode_degree  <  var_124_temp2.roops_core_objects_BinomialHeapNode_degree;
                                                            if (t_699) {
                                                              {
                                                                {
                                                                  {
                                                                    {
                                                                      {
                                                                        boolean t_695;
                                                                        boolean t_696;
                                                                        boolean t_697;

                                                                        {
                                                                          t_696 = var_123_temp1.roops_core_objects_BinomialHeapNode_sibling  ==  null;
                                                                          if (t_696) {
                                                                            {
                                                                              t_695 = true;
                                                                            }
                                                                          } else {
                                                                            {
                                                                              {
                                                                                t_697 = var_123_temp1.roops_core_objects_BinomialHeapNode_sibling.roops_core_objects_BinomialHeapNode_degree  >  var_124_temp2.roops_core_objects_BinomialHeapNode_degree;
                                                                                if (t_697) {
                                                                                  {
                                                                                    t_695 = true;
                                                                                  }
                                                                                } else {
                                                                                  {
                                                                                    t_695 = false;
                                                                                  }
                                                                                }
                                                                              }
                                                                            }
                                                                          }
                                                                        }
                                                                        if (t_695) {
                                                                          {
                                                                            {
                                                                              {
                                                                                {
                                                                                  {
                                                                                    roops.core.objects.BinomialHeapNode var_132_tmp_4_2 = var_124_temp2;

                                                                                    var_124_temp2 = var_124_temp2.roops_core_objects_BinomialHeapNode_sibling;
                                                                                    var_132_tmp_4_2.roops_core_objects_BinomialHeapNode_sibling = var_123_temp1.roops_core_objects_BinomialHeapNode_sibling;
                                                                                    var_123_temp1.roops_core_objects_BinomialHeapNode_sibling = var_132_tmp_4_2;
                                                                                    var_123_temp1 = var_132_tmp_4_2.roops_core_objects_BinomialHeapNode_sibling;
                                                                                  }
                                                                                }
                                                                              }
                                                                            }
                                                                          }
                                                                        } else {
                                                                          {
                                                                            {
                                                                              {
                                                                                {
                                                                                  {
                                                                                    var_123_temp1 = var_123_temp1.roops_core_objects_BinomialHeapNode_sibling;
                                                                                  }
                                                                                }
                                                                              }
                                                                            }
                                                                          }
                                                                        }
                                                                      }
                                                                    }
                                                                  }
                                                                }
                                                              }
                                                            } else {
                                                              {
                                                                {
                                                                  {
                                                                    {
                                                                      {
                                                                        boolean t_698;
                                                                        roops.core.objects.BinomialHeapNode var_133_tmp_4_2 = var_123_temp1;

                                                                        var_123_temp1 = var_124_temp2;
                                                                        var_124_temp2 = var_124_temp2.roops_core_objects_BinomialHeapNode_sibling;
                                                                        var_123_temp1.roops_core_objects_BinomialHeapNode_sibling = var_133_tmp_4_2;
                                                                        t_698 = var_133_tmp_4_2  ==  this.roops_core_objects_BinomialHeap_Nodes;
                                                                        if (t_698) {
                                                                          {
                                                                            {
                                                                              {
                                                                                {
                                                                                  {
                                                                                    this.roops_core_objects_BinomialHeap_Nodes = var_123_temp1;
                                                                                  }
                                                                                }
                                                                              }
                                                                            }
                                                                          }
                                                                        }
                                                                      }
                                                                    }
                                                                  }
                                                                }
                                                              }
                                                            }
                                                          }
                                                        }
                                                      }
                                                    }
                                                  }
                                                }
                                              }
                                              {
                                                t_708 = var_123_temp1  !=  null;
                                                if (t_708) {
                                                  {
                                                    {
                                                      t_709 = var_124_temp2  !=  null;
                                                      if (t_709) {
                                                        {
                                                          t_707 = true;
                                                        }
                                                      } else {
                                                        {
                                                          t_707 = false;
                                                        }
                                                      }
                                                    }
                                                  }
                                                } else {
                                                  {
                                                    t_707 = false;
                                                  }
                                                }
                                              }
                                              if (t_707) {
                                                {
                                                  {
                                                    {
                                                      {
                                                        {
                                                          boolean t_706;

                                                          t_706 = var_123_temp1.roops_core_objects_BinomialHeapNode_degree  ==  var_124_temp2.roops_core_objects_BinomialHeapNode_degree;
                                                          if (t_706) {
                                                            {
                                                              {
                                                                {
                                                                  {
                                                                    {
                                                                      roops.core.objects.BinomialHeapNode var_134_tmp_4_1 = var_124_temp2;

                                                                      var_124_temp2 = var_124_temp2.roops_core_objects_BinomialHeapNode_sibling;
                                                                      var_134_tmp_4_1.roops_core_objects_BinomialHeapNode_sibling = var_123_temp1.roops_core_objects_BinomialHeapNode_sibling;
                                                                      var_123_temp1.roops_core_objects_BinomialHeapNode_sibling = var_134_tmp_4_1;
                                                                      var_123_temp1 = var_134_tmp_4_1.roops_core_objects_BinomialHeapNode_sibling;
                                                                    }
                                                                  }
                                                                }
                                                              }
                                                            }
                                                          } else {
                                                            {
                                                              {
                                                                {
                                                                  {
                                                                    {
                                                                      boolean t_705;

                                                                      t_705 = var_123_temp1.roops_core_objects_BinomialHeapNode_degree  <  var_124_temp2.roops_core_objects_BinomialHeapNode_degree;
                                                                      if (t_705) {
                                                                        {
                                                                          {
                                                                            {
                                                                              {
                                                                                {
                                                                                  boolean t_701;
                                                                                  boolean t_702;
                                                                                  boolean t_703;

                                                                                  {
                                                                                    t_702 = var_123_temp1.roops_core_objects_BinomialHeapNode_sibling  ==  null;
                                                                                    if (t_702) {
                                                                                      {
                                                                                        t_701 = true;
                                                                                      }
                                                                                    } else {
                                                                                      {
                                                                                        {
                                                                                          t_703 = var_123_temp1.roops_core_objects_BinomialHeapNode_sibling.roops_core_objects_BinomialHeapNode_degree  >  var_124_temp2.roops_core_objects_BinomialHeapNode_degree;
                                                                                          if (t_703) {
                                                                                            {
                                                                                              t_701 = true;
                                                                                            }
                                                                                          } else {
                                                                                            {
                                                                                              t_701 = false;
                                                                                            }
                                                                                          }
                                                                                        }
                                                                                      }
                                                                                    }
                                                                                  }
                                                                                  if (t_701) {
                                                                                    {
                                                                                      {
                                                                                        {
                                                                                          {
                                                                                            {
                                                                                              roops.core.objects.BinomialHeapNode var_135_tmp_4_1 = var_124_temp2;

                                                                                              var_124_temp2 = var_124_temp2.roops_core_objects_BinomialHeapNode_sibling;
                                                                                              var_135_tmp_4_1.roops_core_objects_BinomialHeapNode_sibling = var_123_temp1.roops_core_objects_BinomialHeapNode_sibling;
                                                                                              var_123_temp1.roops_core_objects_BinomialHeapNode_sibling = var_135_tmp_4_1;
                                                                                              var_123_temp1 = var_135_tmp_4_1.roops_core_objects_BinomialHeapNode_sibling;
                                                                                            }
                                                                                          }
                                                                                        }
                                                                                      }
                                                                                    }
                                                                                  } else {
                                                                                    {
                                                                                      {
                                                                                        {
                                                                                          {
                                                                                            {
                                                                                              var_123_temp1 = var_123_temp1.roops_core_objects_BinomialHeapNode_sibling;
                                                                                            }
                                                                                          }
                                                                                        }
                                                                                      }
                                                                                    }
                                                                                  }
                                                                                }
                                                                              }
                                                                            }
                                                                          }
                                                                        }
                                                                      } else {
                                                                        {
                                                                          {
                                                                            {
                                                                              {
                                                                                {
                                                                                  boolean t_704;
                                                                                  roops.core.objects.BinomialHeapNode var_136_tmp_4_1 = var_123_temp1;

                                                                                  var_123_temp1 = var_124_temp2;
                                                                                  var_124_temp2 = var_124_temp2.roops_core_objects_BinomialHeapNode_sibling;
                                                                                  var_123_temp1.roops_core_objects_BinomialHeapNode_sibling = var_136_tmp_4_1;
                                                                                  t_704 = var_136_tmp_4_1  ==  this.roops_core_objects_BinomialHeap_Nodes;
                                                                                  if (t_704) {
                                                                                    {
                                                                                      {
                                                                                        {
                                                                                          {
                                                                                            {
                                                                                              this.roops_core_objects_BinomialHeap_Nodes = var_123_temp1;
                                                                                            }
                                                                                          }
                                                                                        }
                                                                                      }
                                                                                    }
                                                                                  }
                                                                                }
                                                                              }
                                                                            }
                                                                          }
                                                                        }
                                                                      }
                                                                    }
                                                                  }
                                                                }
                                                              }
                                                            }
                                                          }
                                                        }
                                                      }
                                                    }
                                                  }
                                                }
                                              }
                                            }
                                          }
                                        }
                                      }
                                    }
                                  }
                                }
                              }
                            }
                          }
                        }
                      }
                    }
                  }
                }
              }
            }
          }
          {
            t_720 = var_123_temp1  !=  null;
            if (t_720) {
              {
                {
                  t_721 = var_124_temp2  !=  null;
                  if (t_721) {
                    {
                      t_719 = true;
                    }
                  } else {
                    {
                      t_719 = false;
                    }
                  }
                }
              }
            } else {
              {
                t_719 = false;
              }
            }
          }
          t_722 = ! t_719;
          assert t_722;
        }
      }
      t_729 = var_123_temp1  ==  null;
      if (t_729) {
        {
          {
            {
              {
                {
                  var_123_temp1 = this.roops_core_objects_BinomialHeap_Nodes;
                  {
                    {
                      boolean t_726;
                      boolean t_727;
                      boolean t_728;

                      t_726 = var_123_temp1.roops_core_objects_BinomialHeapNode_sibling  !=  null;

                      if (t_726) {
                        {
                          {
                            {
                              {
                                {
                                  boolean t_725;

                                  {
                                    var_123_temp1 = var_123_temp1.roops_core_objects_BinomialHeapNode_sibling;
                                  }
                                  t_725 = var_123_temp1.roops_core_objects_BinomialHeapNode_sibling  !=  null;
                                  if (t_725) {
                                    {
                                      {
                                        {
                                          {
                                            {
                                              boolean t_724;

                                              {
                                                var_123_temp1 = var_123_temp1.roops_core_objects_BinomialHeapNode_sibling;
                                              }
                                              t_724 = var_123_temp1.roops_core_objects_BinomialHeapNode_sibling  !=  null;
                                              if (t_724) {
                                                {
                                                  {
                                                    {
                                                      {
                                                        {
                                                          boolean t_723;

                                                          {
                                                            var_123_temp1 = var_123_temp1.roops_core_objects_BinomialHeapNode_sibling;
                                                          }
                                                          t_723 = var_123_temp1.roops_core_objects_BinomialHeapNode_sibling  !=  null;
                                                          if (t_723) {
                                                            {
                                                              {
                                                                {
                                                                  {
                                                                    {
                                                                      var_123_temp1 = var_123_temp1.roops_core_objects_BinomialHeapNode_sibling;
                                                                    }
                                                                  }
                                                                }
                                                              }
                                                            }
                                                          }
                                                        }
                                                      }
                                                    }
                                                  }
                                                }
                                              }
                                            }
                                          }
                                        }
                                      }
                                    }
                                  }
                                }
                              }
                            }
                          }
                        }
                      }
                      t_727 = var_123_temp1.roops_core_objects_BinomialHeapNode_sibling  !=  null;
                      t_728 = ! t_727;
                      assert t_728;
                    }
                  }
                  var_123_temp1.roops_core_objects_BinomialHeapNode_sibling = var_124_temp2;
                }
              }
            }
          }
        }
      }
    }
  }


  private void unionNodes(roops.core.objects.BinomialHeapNode binHeap) {
    roops.core.objects.BinomialHeapNode param_binHeap_24;

    param_binHeap_24 = binHeap;
    {
      this.merge(param_binHeap_24);
      roops.core.objects.BinomialHeapNode var_137_prevTemp = ((roops.core.objects.BinomialHeapNode)(null)), var_138_temp = this.roops_core_objects_BinomialHeap_Nodes, var_139_nextTemp = this.roops_core_objects_BinomialHeap_Nodes.roops_core_objects_BinomialHeapNode_sibling;

      {
        {
          boolean t_769;
          boolean t_770;
          boolean t_771;

          t_769 = var_139_nextTemp  !=  null;

          if (t_769) {
            {
              {
                {
                  {
                    {
                      boolean t_768;

                      {
                        boolean t_734;
                        boolean t_735;
                        boolean t_736;
                        boolean t_737;
                        boolean t_738;

                        {
                          t_735 = var_138_temp.roops_core_objects_BinomialHeapNode_degree  !=  var_139_nextTemp.roops_core_objects_BinomialHeapNode_degree;
                          if (t_735) {
                            {
                              t_734 = true;
                            }
                          } else {
                            {
                              {
                                t_737 = var_139_nextTemp.roops_core_objects_BinomialHeapNode_sibling  !=  null;

                                if (t_737) {
                                  {
                                    {
                                      t_738 = var_139_nextTemp.roops_core_objects_BinomialHeapNode_sibling.roops_core_objects_BinomialHeapNode_degree  ==  var_138_temp.roops_core_objects_BinomialHeapNode_degree;
                                      if (t_738) {
                                        {
                                          t_736 = true;
                                        }
                                      } else {
                                        {
                                          t_736 = false;
                                        }
                                      }
                                    }
                                  }
                                } else {
                                  {
                                    t_736 = false;
                                  }
                                }
                                if (t_736) {
                                  {
                                    t_734 = true;
                                  }
                                } else {
                                  {
                                    t_734 = false;
                                  }
                                }
                              }
                            }
                          }
                        }

                        if (t_734) {
                          {
                            {
                              {
                                {
                                  {
                                    var_137_prevTemp = var_138_temp;
                                    var_138_temp = var_139_nextTemp;
                                  }
                                }
                              }
                            }
                          }
                        } else {
                          {
                            {
                              {
                                {
                                  {
                                    boolean t_733;

                                    t_733 = var_138_temp.roops_core_objects_BinomialHeapNode_key  <=  var_139_nextTemp.roops_core_objects_BinomialHeapNode_key;
                                    if (t_733) {
                                      {
                                        {
                                          {
                                            {
                                              {
                                                int t_730;

                                                var_138_temp.roops_core_objects_BinomialHeapNode_sibling = var_139_nextTemp.roops_core_objects_BinomialHeapNode_sibling;
                                                var_139_nextTemp.roops_core_objects_BinomialHeapNode_parent = var_138_temp;
                                                var_139_nextTemp.roops_core_objects_BinomialHeapNode_sibling = var_138_temp.roops_core_objects_BinomialHeapNode_child;
                                                var_138_temp.roops_core_objects_BinomialHeapNode_child = var_139_nextTemp;
                                                t_730 = var_138_temp.roops_core_objects_BinomialHeapNode_degree;
                                                var_138_temp.roops_core_objects_BinomialHeapNode_degree = var_138_temp.roops_core_objects_BinomialHeapNode_degree + (byte)1;
                                              }
                                            }
                                          }
                                        }
                                      }
                                    } else {
                                      {
                                        {
                                          {
                                            {
                                              {
                                                boolean t_731;
                                                int t_732;

                                                t_731 = var_137_prevTemp  ==  null;

                                                if (t_731) {
                                                  {
                                                    {
                                                      {
                                                        {
                                                          {
                                                            this.roops_core_objects_BinomialHeap_Nodes = var_139_nextTemp;
                                                          }
                                                        }
                                                      }
                                                    }
                                                  }
                                                } else {
                                                  {
                                                    {
                                                      {
                                                        {
                                                          {
                                                            var_137_prevTemp.roops_core_objects_BinomialHeapNode_sibling = var_139_nextTemp;
                                                          }
                                                        }
                                                      }
                                                    }
                                                  }
                                                }
                                                var_138_temp.roops_core_objects_BinomialHeapNode_parent = var_139_nextTemp;
                                                var_138_temp.roops_core_objects_BinomialHeapNode_sibling = var_139_nextTemp.roops_core_objects_BinomialHeapNode_child;
                                                var_139_nextTemp.roops_core_objects_BinomialHeapNode_child = var_138_temp;
                                                t_732 = var_139_nextTemp.roops_core_objects_BinomialHeapNode_degree;
                                                var_139_nextTemp.roops_core_objects_BinomialHeapNode_degree = var_139_nextTemp.roops_core_objects_BinomialHeapNode_degree + (byte)1;
                                                var_138_temp = var_139_nextTemp;
                                              }
                                            }
                                          }
                                        }
                                      }
                                    }
                                  }
                                }
                              }
                            }
                          }
                        }
                        var_139_nextTemp = var_138_temp.roops_core_objects_BinomialHeapNode_sibling;
                      }
                      t_768 = var_139_nextTemp  !=  null;
                      if (t_768) {
                        {
                          {
                            {
                              {
                                {
                                  boolean t_767;

                                  {
                                    boolean t_743;
                                    boolean t_744;
                                    boolean t_745;
                                    boolean t_746;
                                    boolean t_747;

                                    {
                                      t_744 = var_138_temp.roops_core_objects_BinomialHeapNode_degree  !=  var_139_nextTemp.roops_core_objects_BinomialHeapNode_degree;
                                      if (t_744) {
                                        {
                                          t_743 = true;
                                        }
                                      } else {
                                        {
                                          {
                                            t_746 = var_139_nextTemp.roops_core_objects_BinomialHeapNode_sibling  !=  null;

                                            if (t_746) {
                                              {
                                                {
                                                  t_747 = var_139_nextTemp.roops_core_objects_BinomialHeapNode_sibling.roops_core_objects_BinomialHeapNode_degree  ==  var_138_temp.roops_core_objects_BinomialHeapNode_degree;
                                                  if (t_747) {
                                                    {
                                                      t_745 = true;
                                                    }
                                                  } else {
                                                    {
                                                      t_745 = false;
                                                    }
                                                  }
                                                }
                                              }
                                            } else {
                                              {
                                                t_745 = false;
                                              }
                                            }
                                            if (t_745) {
                                              {
                                                t_743 = true;
                                              }
                                            } else {
                                              {
                                                t_743 = false;
                                              }
                                            }
                                          }
                                        }
                                      }
                                    }

                                    if (t_743) {
                                      {
                                        {
                                          {
                                            {
                                              {
                                                var_137_prevTemp = var_138_temp;
                                                var_138_temp = var_139_nextTemp;
                                              }
                                            }
                                          }
                                        }
                                      }
                                    } else {
                                      {
                                        {
                                          {
                                            {
                                              {
                                                boolean t_742;

                                                t_742 = var_138_temp.roops_core_objects_BinomialHeapNode_key  <=  var_139_nextTemp.roops_core_objects_BinomialHeapNode_key;
                                                if (t_742) {
                                                  {
                                                    {
                                                      {
                                                        {
                                                          {
                                                            int t_739;

                                                            var_138_temp.roops_core_objects_BinomialHeapNode_sibling = var_139_nextTemp.roops_core_objects_BinomialHeapNode_sibling;
                                                            var_139_nextTemp.roops_core_objects_BinomialHeapNode_parent = var_138_temp;
                                                            var_139_nextTemp.roops_core_objects_BinomialHeapNode_sibling = var_138_temp.roops_core_objects_BinomialHeapNode_child;
                                                            var_138_temp.roops_core_objects_BinomialHeapNode_child = var_139_nextTemp;
                                                            t_739 = var_138_temp.roops_core_objects_BinomialHeapNode_degree;
                                                            var_138_temp.roops_core_objects_BinomialHeapNode_degree = var_138_temp.roops_core_objects_BinomialHeapNode_degree + (byte)1;
                                                          }
                                                        }
                                                      }
                                                    }
                                                  }
                                                } else {
                                                  {
                                                    {
                                                      {
                                                        {
                                                          {
                                                            boolean t_740;
                                                            int t_741;

                                                            t_740 = var_137_prevTemp  ==  null;

                                                            if (t_740) {
                                                              {
                                                                {
                                                                  {
                                                                    {
                                                                      {
                                                                        this.roops_core_objects_BinomialHeap_Nodes = var_139_nextTemp;
                                                                      }
                                                                    }
                                                                  }
                                                                }
                                                              }
                                                            } else {
                                                              {
                                                                {
                                                                  {
                                                                    {
                                                                      {
                                                                        var_137_prevTemp.roops_core_objects_BinomialHeapNode_sibling = var_139_nextTemp;
                                                                      }
                                                                    }
                                                                  }
                                                                }
                                                              }
                                                            }
                                                            var_138_temp.roops_core_objects_BinomialHeapNode_parent = var_139_nextTemp;
                                                            var_138_temp.roops_core_objects_BinomialHeapNode_sibling = var_139_nextTemp.roops_core_objects_BinomialHeapNode_child;
                                                            var_139_nextTemp.roops_core_objects_BinomialHeapNode_child = var_138_temp;
                                                            t_741 = var_139_nextTemp.roops_core_objects_BinomialHeapNode_degree;
                                                            var_139_nextTemp.roops_core_objects_BinomialHeapNode_degree = var_139_nextTemp.roops_core_objects_BinomialHeapNode_degree + (byte)1;
                                                            var_138_temp = var_139_nextTemp;
                                                          }
                                                        }
                                                      }
                                                    }
                                                  }
                                                }
                                              }
                                            }
                                          }
                                        }
                                      }
                                    }
                                    var_139_nextTemp = var_138_temp.roops_core_objects_BinomialHeapNode_sibling;
                                  }
                                  t_767 = var_139_nextTemp  !=  null;
                                  if (t_767) {
                                    {
                                      {
                                        {
                                          {
                                            {
                                              boolean t_766;

                                              {
                                                boolean t_752;
                                                boolean t_753;
                                                boolean t_754;
                                                boolean t_755;
                                                boolean t_756;

                                                {
                                                  t_753 = var_138_temp.roops_core_objects_BinomialHeapNode_degree  !=  var_139_nextTemp.roops_core_objects_BinomialHeapNode_degree;
                                                  if (t_753) {
                                                    {
                                                      t_752 = true;
                                                    }
                                                  } else {
                                                    {
                                                      {
                                                        t_755 = var_139_nextTemp.roops_core_objects_BinomialHeapNode_sibling  !=  null;

                                                        if (t_755) {
                                                          {
                                                            {
                                                              t_756 = var_139_nextTemp.roops_core_objects_BinomialHeapNode_sibling.roops_core_objects_BinomialHeapNode_degree  ==  var_138_temp.roops_core_objects_BinomialHeapNode_degree;
                                                              if (t_756) {
                                                                {
                                                                  t_754 = true;
                                                                }
                                                              } else {
                                                                {
                                                                  t_754 = false;
                                                                }
                                                              }
                                                            }
                                                          }
                                                        } else {
                                                          {
                                                            t_754 = false;
                                                          }
                                                        }
                                                        if (t_754) {
                                                          {
                                                            t_752 = true;
                                                          }
                                                        } else {
                                                          {
                                                            t_752 = false;
                                                          }
                                                        }
                                                      }
                                                    }
                                                  }
                                                }

                                                if (t_752) {
                                                  {
                                                    {
                                                      {
                                                        {
                                                          {
                                                            var_137_prevTemp = var_138_temp;
                                                            var_138_temp = var_139_nextTemp;
                                                          }
                                                        }
                                                      }
                                                    }
                                                  }
                                                } else {
                                                  {
                                                    {
                                                      {
                                                        {
                                                          {
                                                            boolean t_751;

                                                            t_751 = var_138_temp.roops_core_objects_BinomialHeapNode_key  <=  var_139_nextTemp.roops_core_objects_BinomialHeapNode_key;
                                                            if (t_751) {
                                                              {
                                                                {
                                                                  {
                                                                    {
                                                                      {
                                                                        int t_748;

                                                                        var_138_temp.roops_core_objects_BinomialHeapNode_sibling = var_139_nextTemp.roops_core_objects_BinomialHeapNode_sibling;
                                                                        var_139_nextTemp.roops_core_objects_BinomialHeapNode_parent = var_138_temp;
                                                                        var_139_nextTemp.roops_core_objects_BinomialHeapNode_sibling = var_138_temp.roops_core_objects_BinomialHeapNode_child;
                                                                        var_138_temp.roops_core_objects_BinomialHeapNode_child = var_139_nextTemp;
                                                                        t_748 = var_138_temp.roops_core_objects_BinomialHeapNode_degree;
                                                                        var_138_temp.roops_core_objects_BinomialHeapNode_degree = var_138_temp.roops_core_objects_BinomialHeapNode_degree + (byte)1;
                                                                      }
                                                                    }
                                                                  }
                                                                }
                                                              }
                                                            } else {
                                                              {
                                                                {
                                                                  {
                                                                    {
                                                                      {
                                                                        boolean t_749;
                                                                        int t_750;

                                                                        t_749 = var_137_prevTemp  ==  null;

                                                                        if (t_749) {
                                                                          {
                                                                            {
                                                                              {
                                                                                {
                                                                                  {
                                                                                    this.roops_core_objects_BinomialHeap_Nodes = var_139_nextTemp;
                                                                                  }
                                                                                }
                                                                              }
                                                                            }
                                                                          }
                                                                        } else {
                                                                          {
                                                                            {
                                                                              {
                                                                                {
                                                                                  {
                                                                                    var_137_prevTemp.roops_core_objects_BinomialHeapNode_sibling = var_139_nextTemp;
                                                                                  }
                                                                                }
                                                                              }
                                                                            }
                                                                          }
                                                                        }
                                                                        var_138_temp.roops_core_objects_BinomialHeapNode_parent = var_139_nextTemp;
                                                                        var_138_temp.roops_core_objects_BinomialHeapNode_sibling = var_139_nextTemp.roops_core_objects_BinomialHeapNode_child;
                                                                        var_139_nextTemp.roops_core_objects_BinomialHeapNode_child = var_138_temp;
                                                                        t_750 = var_139_nextTemp.roops_core_objects_BinomialHeapNode_degree;
                                                                        var_139_nextTemp.roops_core_objects_BinomialHeapNode_degree = var_139_nextTemp.roops_core_objects_BinomialHeapNode_degree + (byte)1;
                                                                        var_138_temp = var_139_nextTemp;
                                                                      }
                                                                    }
                                                                  }
                                                                }
                                                              }
                                                            }
                                                          }
                                                        }
                                                      }
                                                    }
                                                  }
                                                }
                                                var_139_nextTemp = var_138_temp.roops_core_objects_BinomialHeapNode_sibling;
                                              }
                                              t_766 = var_139_nextTemp  !=  null;
                                              if (t_766) {
                                                {
                                                  {
                                                    {
                                                      {
                                                        {
                                                          boolean t_761;
                                                          boolean t_762;
                                                          boolean t_763;
                                                          boolean t_764;
                                                          boolean t_765;

                                                          {
                                                            t_762 = var_138_temp.roops_core_objects_BinomialHeapNode_degree  !=  var_139_nextTemp.roops_core_objects_BinomialHeapNode_degree;
                                                            if (t_762) {
                                                              {
                                                                t_761 = true;
                                                              }
                                                            } else {
                                                              {
                                                                {
                                                                  t_764 = var_139_nextTemp.roops_core_objects_BinomialHeapNode_sibling  !=  null;

                                                                  if (t_764) {
                                                                    {
                                                                      {
                                                                        t_765 = var_139_nextTemp.roops_core_objects_BinomialHeapNode_sibling.roops_core_objects_BinomialHeapNode_degree  ==  var_138_temp.roops_core_objects_BinomialHeapNode_degree;
                                                                        if (t_765) {
                                                                          {
                                                                            t_763 = true;
                                                                          }
                                                                        } else {
                                                                          {
                                                                            t_763 = false;
                                                                          }
                                                                        }
                                                                      }
                                                                    }
                                                                  } else {
                                                                    {
                                                                      t_763 = false;
                                                                    }
                                                                  }
                                                                  if (t_763) {
                                                                    {
                                                                      t_761 = true;
                                                                    }
                                                                  } else {
                                                                    {
                                                                      t_761 = false;
                                                                    }
                                                                  }
                                                                }
                                                              }
                                                            }
                                                          }

                                                          if (t_761) {
                                                            {
                                                              {
                                                                {
                                                                  {
                                                                    {
                                                                      var_137_prevTemp = var_138_temp;
                                                                      var_138_temp = var_139_nextTemp;
                                                                    }
                                                                  }
                                                                }
                                                              }
                                                            }
                                                          } else {
                                                            {
                                                              {
                                                                {
                                                                  {
                                                                    {
                                                                      boolean t_760;

                                                                      t_760 = var_138_temp.roops_core_objects_BinomialHeapNode_key  <=  var_139_nextTemp.roops_core_objects_BinomialHeapNode_key;
                                                                      if (t_760) {
                                                                        {
                                                                          {
                                                                            {
                                                                              {
                                                                                {
                                                                                  int t_757;

                                                                                  var_138_temp.roops_core_objects_BinomialHeapNode_sibling = var_139_nextTemp.roops_core_objects_BinomialHeapNode_sibling;
                                                                                  var_139_nextTemp.roops_core_objects_BinomialHeapNode_parent = var_138_temp;
                                                                                  var_139_nextTemp.roops_core_objects_BinomialHeapNode_sibling = var_138_temp.roops_core_objects_BinomialHeapNode_child;
                                                                                  var_138_temp.roops_core_objects_BinomialHeapNode_child = var_139_nextTemp;
                                                                                  t_757 = var_138_temp.roops_core_objects_BinomialHeapNode_degree;
                                                                                  var_138_temp.roops_core_objects_BinomialHeapNode_degree = var_138_temp.roops_core_objects_BinomialHeapNode_degree + (byte)1;
                                                                                }
                                                                              }
                                                                            }
                                                                          }
                                                                        }
                                                                      } else {
                                                                        {
                                                                          {
                                                                            {
                                                                              {
                                                                                {
                                                                                  boolean t_758;
                                                                                  int t_759;

                                                                                  t_758 = var_137_prevTemp  ==  null;

                                                                                  if (t_758) {
                                                                                    {
                                                                                      {
                                                                                        {
                                                                                          {
                                                                                            {
                                                                                              this.roops_core_objects_BinomialHeap_Nodes = var_139_nextTemp;
                                                                                            }
                                                                                          }
                                                                                        }
                                                                                      }
                                                                                    }
                                                                                  } else {
                                                                                    {
                                                                                      {
                                                                                        {
                                                                                          {
                                                                                            {
                                                                                              var_137_prevTemp.roops_core_objects_BinomialHeapNode_sibling = var_139_nextTemp;
                                                                                            }
                                                                                          }
                                                                                        }
                                                                                      }
                                                                                    }
                                                                                  }
                                                                                  var_138_temp.roops_core_objects_BinomialHeapNode_parent = var_139_nextTemp;
                                                                                  var_138_temp.roops_core_objects_BinomialHeapNode_sibling = var_139_nextTemp.roops_core_objects_BinomialHeapNode_child;
                                                                                  var_139_nextTemp.roops_core_objects_BinomialHeapNode_child = var_138_temp;
                                                                                  t_759 = var_139_nextTemp.roops_core_objects_BinomialHeapNode_degree;
                                                                                  var_139_nextTemp.roops_core_objects_BinomialHeapNode_degree = var_139_nextTemp.roops_core_objects_BinomialHeapNode_degree + (byte)1;
                                                                                  var_138_temp = var_139_nextTemp;
                                                                                }
                                                                              }
                                                                            }
                                                                          }
                                                                        }
                                                                      }
                                                                    }
                                                                  }
                                                                }
                                                              }
                                                            }
                                                          }
                                                          var_139_nextTemp = var_138_temp.roops_core_objects_BinomialHeapNode_sibling;
                                                        }
                                                      }
                                                    }
                                                  }
                                                }
                                              }
                                            }
                                          }
                                        }
                                      }
                                    }
                                  }
                                }
                              }
                            }
                          }
                        }
                      }
                    }
                  }
                }
              }
            }
          }
          t_770 = var_139_nextTemp  !=  null;
          t_771 = ! t_770;
          assert t_771;
        }
      }
    }
  }


  /*@ 
    @ requires this.roops_core_objects_BinomialHeap_Nodes  !=  null;
    @ ensures (\exists roops.core.objects.BinomialHeapNode n; \reach(this.roops_core_objects_BinomialHeap_Nodes, roops.core.objects.BinomialHeapNode, roops_core_objects_BinomialHeapNode_sibling + roops_core_objects_BinomialHeapNode_child).has(((java.lang.Object)(n)))  ==  true; n.roops_core_objects_BinomialHeapNode_key  ==  \result);
    @ ensures (\forall roops.core.objects.BinomialHeapNode n; \reach(this.roops_core_objects_BinomialHeap_Nodes, roops.core.objects.BinomialHeapNode, roops_core_objects_BinomialHeapNode_sibling + roops_core_objects_BinomialHeapNode_child).has(((java.lang.Object)(n)))  ==  true; \result  <=  n.roops_core_objects_BinomialHeapNode_key);
    @ ensures (\forall roops.core.objects.BinomialHeapNode n; \reach(this.roops_core_objects_BinomialHeap_Nodes, roops.core.objects.BinomialHeapNode, roops_core_objects_BinomialHeapNode_sibling + roops_core_objects_BinomialHeapNode_child).has(((java.lang.Object)(n)))  ==  true; \old(n.roops_core_objects_BinomialHeapNode_key)  ==  n.roops_core_objects_BinomialHeapNode_key);
    @ ensures (\forall roops.core.objects.BinomialHeapNode n; \reach(this.roops_core_objects_BinomialHeap_Nodes, roops.core.objects.BinomialHeapNode, roops_core_objects_BinomialHeapNode_sibling + roops_core_objects_BinomialHeapNode_child).has(((java.lang.Object)(n)))  ==  true; \old(n.roops_core_objects_BinomialHeapNode_degree)  ==  n.roops_core_objects_BinomialHeapNode_degree);
    @ ensures (\forall roops.core.objects.BinomialHeapNode n; \reach(this.roops_core_objects_BinomialHeap_Nodes, roops.core.objects.BinomialHeapNode, roops_core_objects_BinomialHeapNode_sibling + roops_core_objects_BinomialHeapNode_child).has(((java.lang.Object)(n)))  ==  true; \old(n.roops_core_objects_BinomialHeapNode_parent)  ==  n.roops_core_objects_BinomialHeapNode_parent);
    @ ensures (\forall roops.core.objects.BinomialHeapNode n; \reach(this.roops_core_objects_BinomialHeap_Nodes, roops.core.objects.BinomialHeapNode, roops_core_objects_BinomialHeapNode_sibling + roops_core_objects_BinomialHeapNode_child).has(((java.lang.Object)(n)))  ==  true; \old(n.roops_core_objects_BinomialHeapNode_sibling)  ==  n.roops_core_objects_BinomialHeapNode_sibling);
    @ ensures (\forall roops.core.objects.BinomialHeapNode n; \reach(this.roops_core_objects_BinomialHeap_Nodes, roops.core.objects.BinomialHeapNode, roops_core_objects_BinomialHeapNode_sibling + roops_core_objects_BinomialHeapNode_child).has(((java.lang.Object)(n)))  ==  true; \old(n.roops_core_objects_BinomialHeapNode_child)  ==  n.roops_core_objects_BinomialHeapNode_child);
    @ signals (java.lang.Exception e) false;
    @*/
  public int findMinimum() {
    {
      {
        roops.core.objects.BinomialHeapNode var_140_x = this.roops_core_objects_BinomialHeap_Nodes;
        roops.core.objects.BinomialHeapNode var_141_y = this.roops_core_objects_BinomialHeap_Nodes;
        int var_142_min = var_140_x.roops_core_objects_BinomialHeapNode_key;

        {
          {
            boolean t_779;
            boolean t_780;
            boolean t_781;

            t_779 = var_140_x  !=  null;

            if (t_779) {
              {
                {
                  {
                    {
                      {
                        boolean t_778;

                        {
                          boolean t_772;

                          t_772 = var_140_x.roops_core_objects_BinomialHeapNode_key  <  var_142_min;

                          if (t_772) {
                            {
                              {
                                {
                                  {
                                    {
                                      var_141_y = var_140_x;
                                      var_142_min = var_140_x.roops_core_objects_BinomialHeapNode_key;
                                    }
                                  }
                                }
                              }
                            }
                          }
                          var_140_x = var_140_x.roops_core_objects_BinomialHeapNode_sibling;
                        }
                        t_778 = var_140_x  !=  null;
                        if (t_778) {
                          {
                            {
                              {
                                {
                                  {
                                    boolean t_777;

                                    {
                                      boolean t_773;

                                      t_773 = var_140_x.roops_core_objects_BinomialHeapNode_key  <  var_142_min;

                                      if (t_773) {
                                        {
                                          {
                                            {
                                              {
                                                {
                                                  var_141_y = var_140_x;
                                                  var_142_min = var_140_x.roops_core_objects_BinomialHeapNode_key;
                                                }
                                              }
                                            }
                                          }
                                        }
                                      }
                                      var_140_x = var_140_x.roops_core_objects_BinomialHeapNode_sibling;
                                    }
                                    t_777 = var_140_x  !=  null;
                                    if (t_777) {
                                      {
                                        {
                                          {
                                            {
                                              {
                                                boolean t_776;

                                                {
                                                  boolean t_774;

                                                  t_774 = var_140_x.roops_core_objects_BinomialHeapNode_key  <  var_142_min;

                                                  if (t_774) {
                                                    {
                                                      {
                                                        {
                                                          {
                                                            {
                                                              var_141_y = var_140_x;
                                                              var_142_min = var_140_x.roops_core_objects_BinomialHeapNode_key;
                                                            }
                                                          }
                                                        }
                                                      }
                                                    }
                                                  }
                                                  var_140_x = var_140_x.roops_core_objects_BinomialHeapNode_sibling;
                                                }
                                                t_776 = var_140_x  !=  null;
                                                if (t_776) {
                                                  {
                                                    {
                                                      {
                                                        {
                                                          {
                                                            boolean t_775;

                                                            t_775 = var_140_x.roops_core_objects_BinomialHeapNode_key  <  var_142_min;

                                                            if (t_775) {
                                                              {
                                                                {
                                                                  {
                                                                    {
                                                                      {
                                                                        var_141_y = var_140_x;
                                                                        var_142_min = var_140_x.roops_core_objects_BinomialHeapNode_key;
                                                                      }
                                                                    }
                                                                  }
                                                                }
                                                              }
                                                            }
                                                            var_140_x = var_140_x.roops_core_objects_BinomialHeapNode_sibling;
                                                          }
                                                        }
                                                      }
                                                    }
                                                  }
                                                }
                                              }
                                            }
                                          }
                                        }
                                      }
                                    }
                                  }
                                }
                              }
                            }
                          }
                        }
                      }
                    }
                  }
                }
              }
            }
            t_780 = var_140_x  !=  null;
            t_781 = ! t_780;
            assert t_781;
          }
        }
        if (true) return var_141_y.roops_core_objects_BinomialHeapNode_key;
      }
    }

    return (byte)0;
  }


  public static void main(java.lang.String[] args) {
    java.lang.String[] param_args_25;

    param_args_25 = args;
    {
      roops.core.objects.BinomialHeap t_782;

      t_782 = new roops.core.objects.BinomialHeap();
      roops.core.objects.BinomialHeap var_143_bh1 = t_782;

      var_143_bh1.insert(3);
      var_143_bh1.insert(3);
      int var_144_s = var_143_bh1.roops_core_objects_BinomialHeap_size;

      System.out.println(var_144_s);
    }
  }

}
