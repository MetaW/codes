//
//  PhysicalScene.swift
//  firstTry
//
//  Created by wanglulu on 15/12/4.
//  Copyright © 2015年 wanglulu. All rights reserved.
//
/************************************
小结：
1.如果不想对物理世界有影响又不想受物理世界的影响，即像幽灵一样
  则不要设置physicalBody即可(背景)
2.如果想对物理世界有影响但不想受物理世界的影响，即作用是单方向的或
  该物体质量无穷大，则要设置physicalBody并将dynamic属性设为false(墙等)
3.如果即想对物理世界有影响又想受到物理世界的影响则需要设置physicalBody并将
  dynamic设为true(一般Sprite)

*************************************/
import Foundation
import SpriteKit

class PhysicalScene: SKScene
{
    override func didMoveToView(view: SKView) {
        
        self.size = CGSize(width: 1024, height: 800)
        
        //
        self.physicsWorld.gravity = CGVectorMake(0, -9.8)
        
        //
        let sceneBody = SKPhysicsBody(edgeLoopFromRect: self.frame)
        sceneBody.friction = 0
        self.physicsBody = sceneBody
        
        let plane = SKSpriteNode(imageNamed: "Spaceship")
        plane.size = CGSize(width: 150,height: 150)
        plane.position = CGPointMake(self.frame.size.width/2, self.frame.size.height/2)
        
        //
        plane.physicsBody = SKPhysicsBody(rectangleOfSize: (plane.size))
        plane.physicsBody?.affectedByGravity = false
        plane.physicsBody?.dynamic = false
        plane.physicsBody?.friction = 0
        
        let rotateAct = SKAction.rotateByAngle(CGFloat(M_PI), duration: 10)
        plane.runAction(SKAction.repeatActionForever(rotateAct))
        
        self.addChild(plane)
        
        //
        let anotherPlan = SKSpriteNode(imageNamed: "Spaceship.png")
        anotherPlan.position = CGPoint(x: 300, y: 700)
        anotherPlan.size = CGSize(width: 200, height: 200)
        
        //!!!!!!用材质自身的像素区域来确定physicalBosy的边缘，耗费资源，最重要的Sprite才考虑用它!!!
        let texture = SKTexture(imageNamed: "Spaceship.png")
        anotherPlan.physicsBody = SKPhysicsBody(texture: texture, size: anotherPlan.size)
        
        anotherPlan.physicsBody?.affectedByGravity = true
        anotherPlan.physicsBody?.restitution = 1
        anotherPlan.physicsBody?.friction = 0
        anotherPlan.physicsBody?.linearDamping = 0
        
        self.addChild(anotherPlan)
        
        
    }
    
    override func touchesBegan(touches: Set<UITouch>, withEvent event: UIEvent?) {
        for touch: AnyObject in touches{
            //
            let posi = touch.locationInNode(self)
            
            //
            let nodeTouched = nodeAtPoint(posi)
            
            //
            if let node = nodeTouched as? SKSpriteNode{
                
                //
                let disappearAnima = SKAction.scaleTo(0.01, duration: 1)
                node.runAction(disappearAnima, completion: { ()->() in
                    //
                    node.removeFromParent()
                })
                
            }else{
                createBall(posi)
            }
            
            
        }
    }
    
    func createBall(posi:CGPoint)->()
    {
        let ball = SKSpriteNode(imageNamed: "huaji")
        ball.size = CGSize(width: 100, height: 100)
        ball.position = posi
        
        ball.physicsBody = SKPhysicsBody(circleOfRadius: 50)
        //
        ball.physicsBody?.affectedByGravity = true
        ball.physicsBody!.restitution = 1 //energy left after a bunciness:0 no left,1 no lose
        ball.physicsBody?.friction = 0  //0~1,default 0.2
        ball.physicsBody?.linearDamping = 0 //another: angularDamping
        ball.physicsBody?.mass = 1
        //other property:
        //  density
        //  mass
        //  velocity
        
        self.addChild(ball)
        
        //追加效果,追加效果必须在Sprite添加到父结点之后施加才会有效果！！！
        ball.physicsBody?.applyImpulse(CGVector(dx: 50 , dy: 50)) //动量
        //other:
        //ball.physicsBody?.applyForce(force: CGVector)
        //ball.physicsBody?.applyAngularImpulse(impulse: CGFloat)

    }
}